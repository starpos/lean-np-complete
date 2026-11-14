module

public meta import Lean.Elab.Command
public meta import NPComplete.Meta.StageDiscipline
public meta import NPComplete.Meta.ApiLayerCheck

/-!
# Checker for the stage discipline

`#check_stage_discipline ns A B` checks every declaration of the current module whose name lies
under namespace `A` or `B`.  Each such declaration must carry exactly one of the tags of
`StageDiscipline.lean`, and the tag decides what it may mention.

* `stage_layout` and `stage_impl` declarations are not restricted: they are the places that own the
  register numbers and the raw semantics.
* `stage_contract` declarations are the published contracts of an implementation.  Only the
  statement (the type, and the body of a definition) is checked, like a boundary; the proof is free.
* `stage_boundary` declarations (facts, programs written against a layout, compositions) are
  checked in the type, in the body and in proofs.

A checked declaration must not
1. contain a register number: a numeric literal as the register of `Expr.reg`, as the target of
   `Program.assign`, `Program.lookup` and `Program.scanList`, as the whole address of
   `Program.assignInd` or `Expr.regInd`, or as the argument of a `Store`.  Data values (`.const 2`),
   iteration counts and numbers elsewhere are allowed;
2. mention `writeReg`, `emptyStore`, `bitInputStore`, the evaluation function of programs or one of
   its unfolding lemmas, build a `Store` by a lambda, or pass a closed `Store` to a function;
3. mention a `stage_impl` or `stage_adapter` declaration, or an in-scope declaration that carries no
   tag.

A layout accessor, a fact or a contract is a boundary of the check: it is classified once where it
is defined and never unfolded here.

What is not detected: a register number hidden behind a definition outside the checked namespaces,
an arithmetic expression on non-literal data that evaluates to a register, memory addresses written
as numerals (except a bare numeral address), a numeral that reaches a register through
`simp`-normalised proof terms that a user never wrote, and whether two definitions of a program
agree.  The proof of a lemma is read from the environment, so a declaration of an imported module
whose proof is hidden by the module system is checked by its statement only.
-/

open Lean Elab Command Meta

public meta section

namespace NPComplete.StageDiscipline

/-- The classes of the tags. -/
inductive Cls where
  | layout
  | impl
  | contract
  | boundary
  | adapter
  deriving BEq, Inhabited

def Cls.toString : Cls → String
  | .layout => "stage_layout"
  | .impl => "stage_impl"
  | .contract => "stage_contract"
  | .boundary => "stage_boundary"
  | .adapter => "stage_adapter"

def clsAttrs : List (Cls × TagAttribute) :=
  [(.layout, stageLayoutAttr), (.impl, stageImplAttr), (.contract, stageContractAttr),
    (.boundary, stageBoundaryAttr), (.adapter, stageAdapterAttr)]

/-- All classes a declaration carries; a well-formed declaration carries one. -/
def classesOf (env : Environment) (n : Name) : List Cls :=
  clsAttrs.filterMap fun (c, a) => if a.hasTag env n then some c else none

/-- Classes that a declaration of the given class must not mention. -/
def forbidden (c : Cls) : Cls → Bool
  | .impl | .adapter => c == .boundary || c == .contract
  | _ => false

/-- Names of a class that is accounted to the inductive type they are generated for. -/
def deriveClasses : List Name := [``Repr, ``DecidableEq, ``BEq, ``Inhabited, ``Hashable, ``Ord, ``Nonempty]

/-- Helpers that `deriving` and the `inductive` command generate under the type's name. -/
def isDeriveHelper (s : String) : Bool :=
  ["ctorElim", "ctorElimType", "noConfusionType", "noConfusion", "sizeOf_spec", "_sizeOf_1"].contains s
    || s.startsWith "toCtorIdx" || s.startsWith "ofNat" || s.endsWith "ctorIdx"
    || s.startsWith "ctorIdx"

/-- The user-level declaration a constant is accounted to: constructors, projections, recursors and
generated helpers of an inductive type map to the type, the instances that `deriving` creates map
to the type they are for, and generated auxiliary definitions map to the declaration they come
from. -/
def accountOwner (env : Environment) (c : Name) : Name :=
  let u := NPComplete.ApiLayer.layerCheckName c
  if isPrivateName c && u.isInternalDetail then NPComplete.ApiLayer.stripInternal u
  else
  let o := NPComplete.ApiLayer.owner env c
  if o != c then o
  else
    let isInst := (instanceExtension.getState env).instanceNames.contains c
    let derived : Option Name := do
      guard isInst
      let ci ← env.find? c
      let e := NPComplete.ApiLayer.instanceResult ci.type
      let cls ← e.getAppFn.constName?
      guard (deriveClasses.contains cls)
      let arg ← e.getAppArgs[0]?
      let t ← arg.getAppFn.constName?
      let .inductInfo _ ← env.find? t | none
      return t
    match derived with
    | some t => t
    | none =>
      match c with
      | .str p s =>
        match env.find? p with
        | some (.inductInfo _) => if isDeriveHelper s then p else c
        | _ => c
      | _ => c

/-- Is the name under one of the namespaces? -/
def inNs (nss : Array Name) (n : Name) : Bool :=
  let n := NPComplete.ApiLayer.layerCheckName n
  nss.any fun ns => ns.isPrefixOf n

/-- The declarations of the current module that the check covers. -/
def scopeOf (env : Environment) (nss : Array Name) : Array Name :=
  let all := env.constants.map₂.foldl (fun (acc : Array Name) n _ => acc.push n) #[]
  (all.filter fun n =>
    inNs nss n && !n.isInternalDetail && accountOwner env n == n
      && !(isAuxRecursor env n) && !(isNoConfusion env n)).qsort Name.lt

/-! ### Syntactic checks -/

/-- A closed natural number literal or arithmetic on such literals. -/
partial def isNumeral : Expr → Bool
  | .lit (.natVal _) => true
  | .mdata _ e => isNumeral e
  | e =>
    match e.getAppFn.constName?, e.getAppArgs with
    | some ``OfNat.ofNat, #[_, .lit (.natVal _), _] => true
    | some ``instOfNatNat, #[.lit (.natVal _)] => true
    | some ``Nat.zero, #[] => true
    | some ``Nat.succ, #[a] => isNumeral a
    | some ``HAdd.hAdd, #[_, _, _, _, a, b] => isNumeral a && isNumeral b
    | some ``HMul.hMul, #[_, _, _, _, a, b] => isNumeral a && isNumeral b
    | some ``HSub.hSub, #[_, _, _, _, a, b] => isNumeral a && isNumeral b
    | _, _ => false

/-- A bare constant address: `Expr.const <numeral>` (data values elsewhere are fine). -/
def isConstNumeral (e : Expr) : Bool :=
  match e.consumeMData.getAppFn.constName?, e.consumeMData.getAppArgs with
  | some `NPComplete.BoundedWhile.Expr.const, #[a] => isNumeral a
  | _, _ => false

def isStoreType (t : Expr) : Bool :=
  t.consumeMData.isConstOf `NPComplete.BoundedWhile.Store

/-- Raw semantics of stores and programs, and the contract entries whose obligations are stated on
raw stores; only an implementation may use them. -/
def isRaw (c : Name) : Bool :=
  let bw := `NPComplete.BoundedWhile
  let rm := `NPComplete.RAMToTM
  let direct : List Name :=
    [`writeReg, `writeReg_same, `writeReg_diff, `emptyStore, `bitInputStore, `Program.eval,
      `Expr.eval, `loopEval, `scanListEval, `StageSpec.of_avoids, `StageSpec.of_writesIn,
      `StageSpec.assign, `LayoutSpec.of_direct, `LayoutSpec.assign, `LayoutSpec.assignCell]
  (direct.any fun d => c == bw ++ d || c == rm ++ d) ||
    ((bw.isPrefixOf c || rm.isPrefixOf c) &&
      (match c with
        | .str _ s => ["eval_", "loopEval_", "scanListEval_"].any (s.startsWith ·)
        | _ => false))

abbrev M := StateRefT (Array String) MetaM

def note (s : String) : M Unit := modify fun a => if a.contains s then a else a.push s

/-- Number-of-register positions of an application `fn args`. -/
def checkRegPositions (fn : Expr) (args : Array Expr) : M Unit := do
  let some c := fn.constName? | return
  let bw := `NPComplete.BoundedWhile
  let num (i : Nat) (what : String) : M Unit := do
    if let some a := args[i]? then
      if isNumeral a then note s!"a numeric register in {what}"
  if c == bw ++ `Expr.reg then num 0 "`Expr.reg`"
  else if c == bw ++ `Program.assign then num 0 "the target of `Program.assign`"
  else if c == bw ++ `Program.lookup then
    num 1 "a register of `Program.lookup`"; num 2 "a register of `Program.lookup`"
  else if c == bw ++ `Program.scanList then num 1 "the register of `Program.scanList`"
  else if c == bw ++ `Expr.regInd then
    if let some a := args[0]? then
      if isNumeral a || isConstNumeral a then note "a numeric address in `Expr.regInd`"
  else if c == bw ++ `Program.assignInd then
    if let some a := args[0]? then
      if isConstNumeral a then note "a numeric address in `Program.assignInd`"

/-- Store-typed positions: application of a store to a numeral, and a concrete store passed as an
argument. -/
def checkStorePositions (fn : Expr) (args : Array Expr) : M Unit := do
  for h : i in [0:args.size] do
    let a := args[i]
    let isNum := isNumeral a
    let isConcrete := a.consumeMData.isLambda ||
      (!a.hasFVar && !a.hasMVar && !a.hasLooseBVars && !a.isSort && a.getAppFn.isConst &&
        !isNum)
    unless isNum || isConcrete do continue
    let pre := mkAppN fn (args.extract 0 i)
    let some ty ← (try some <$> inferType pre catch _ => pure none) | continue
    if isNum && isStoreType ty then
      note "a numeral applied to a `Store`"
    else if isConcrete then
      let ty ← whnfR ty
      if ty.isForall && isStoreType ty.bindingDomain! then
        note "a closed `Store` passed as an argument"

partial def visit (e : Expr) : M Unit := do
  match e with
  | .lam n t b bi => visit t; withLocalDecl n bi t fun x => visit (b.instantiate1 x)
  | .forallE n t b bi => visit t; withLocalDecl n bi t fun x => visit (b.instantiate1 x)
  | .letE n t v b _ =>
    visit t; visit v
    withLetDecl n t v fun x => visit (b.instantiate1 x)
  | .mdata _ b => visit b
  | .proj _ _ b => visit b
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    checkRegPositions fn args
    checkStorePositions fn args
    unless fn.isConst || fn.isFVar do visit fn
    for a in args do visit a
  | _ => pure ()

/-- Constants of `e`, with generated auxiliary declarations mapped to their source. -/
def usedOwners (env : Environment) (e : Expr) : Array Name :=
  e.getUsedConstants.foldl (fun (acc : Array Name) c =>
    let d := accountOwner env c
    if acc.contains d then acc else acc.push d) #[]

/-- Does the body build a `Store` by a lambda: a definition whose result type is `Store`? -/
def buildsStore (ty value : Expr) : Bool :=
  let rec arity : Expr → Nat
    | .forallE _ _ b _ => arity b + 1
    | _ => 0
  let rec resultType : Expr → Expr
    | .forallE _ _ b _ => resultType b
    | t => t
  let rec strip : Nat → Expr → Expr
    | 0, v => v
    | k + 1, .lam _ _ b _ => strip k b
    | _, v => v
  isStoreType (resultType ty) && (strip (arity ty) value.consumeMData).consumeMData.isLambda

/-- The parts of a declaration that a class inspects: label, expression, whether it is a proof. -/
def partsOf (env : Environment) (n : Name) (c : Cls) : Array (String × Expr) := Id.run do
  let some ci := env.find? n | return #[]
  let mut ps : Array (String × Expr) := #[("type", ci.type)]
  let value? : Option Expr := match ci with
    | .defnInfo d => some d.value
    | .thmInfo t => some t.value
    | _ => none
  if let some v := value? then
    if c == .boundary || (c == .contract && ci matches .defnInfo _) then
      ps := ps.push ("body", v)
  -- generated auxiliary definitions that hold the real body of `n`
  if c == .boundary || c == .contract then
    for aux in env.constants.map₂.foldl (fun (acc : Array Name) m _ => acc.push m) #[] do
      if let some b := NPComplete.ApiLayer.auxBody? env n aux then
        ps := ps.push ("body", b)
  return ps

/-- Violations of the discipline for the declaration `n` of class `c`. -/
def violationsOf (env : Environment) (nss : Array Name) (n : Name) (c : Cls) :
    MetaM (Array String) := do
  let disp := NPComplete.ApiLayer.layerCheckName n
  let mut out : Array String := #[]
  if c == .layout || c == .impl || c == .adapter then return out
  for (where_, e) in partsOf env n c do
    let (_, found) ← (visit e).run #[]
    for f in found do
      out := out.push s!"{c.toString} declaration `{disp}` has {f} in its {where_}"
    if where_ == "body" then
      let ci := (env.find? n).get!
      if let .defnInfo d := ci then
        if buildsStore d.type e then
          out := out.push s!"{c.toString} declaration `{disp}` builds a `Store` by a lambda"
    let mut seen : NameSet := {}
    for d in usedOwners env e do
      if NPComplete.ApiLayer.layerCheckName d == disp || seen.contains d then continue
      seen := seen.insert d
      let dd := NPComplete.ApiLayer.layerCheckName d
      if isRaw dd then
        out := out.push s!"{c.toString} declaration `{disp}` mentions the raw store operation `{dd}` in its {where_}"
      else
        match classesOf env d with
        | [] =>
          if inNs nss d then
            out := out.push s!"{c.toString} declaration `{disp}` mentions unclassified `{dd}` in its {where_}"
        | cs =>
          if cs.any (forbidden c) then
            out := out.push s!"{c.toString} declaration `{disp}` mentions {", ".intercalate (cs.map Cls.toString)} `{dd}` in its {where_}"
  return out

syntax (name := checkStageDiscipline) "#check_stage_discipline" (&"ns" (ppSpace ident)+)? : command

@[command_elab checkStageDiscipline] def elabCheckStageDiscipline : CommandElab := fun stx => do
  let env ← getEnv
  let nss : Array Name := if stx[1].getArgs.isEmpty then #[] else
    stx[1][1].getArgs.map (·.getId)
  if nss.isEmpty then
    logErrorAt stx "`#check_stage_discipline` needs `ns` followed by at least one namespace"
    return
  for n in scopeOf env nss do
    let disp := NPComplete.ApiLayer.layerCheckName n
    match classesOf env n with
    | [] => logErrorAt stx s!"declaration `{disp}` is not classified (stage_layout, stage_impl, stage_contract or stage_boundary)"
    | [c] =>
      let vs ← liftTermElabM (violationsOf env nss n c)
      for v in vs do logErrorAt stx v
    | cs => logErrorAt stx s!"declaration `{disp}` carries more than one classification: {", ".intercalate (cs.map Cls.toString)}"

end NPComplete.StageDiscipline
