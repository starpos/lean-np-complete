module

public meta import Lean.Elab.Command
public meta import NPComplete.Meta.ApiLayer

/-!
# Checker for the API layering

`#check_api_layers` verifies that the statement of every tagged declaration mentions only
declarations of a layer it may depend on, so that no internal type leaks into the public surface.

* A `stable_api` declaration may mention only `stable_api` declarations of `NPComplete`.
* A `construction_api` declaration may mention `stable_api` and `construction_api` declarations.
* Constants outside the `NPComplete` namespace (Lean core, Std, Mathlib) are always allowed.

What is inspected is the statement, never a proof: the type of the declaration; for an
inductive type or structure also the types of its constructors; and for a definition whose type
ends in a sort (a predicate or a type, whose body is what its statement means) also the body.
The body of a data-valued definition is an implementation and is not inspected.

Constants that are artifacts of the declaration itself are mapped to the declaration they belong
to before the check: constructors, projections, recursors and `casesOn`/`brecOn`/`noConfusion`
and similar auxiliaries map to their inductive type; matchers, equation lemmas and other
internal-detail names map to the declaration they were generated from. Private names are traced
back to their source names, so private declarations under `NPComplete` participate in the same layer
check. Instances are ordinary constants.

`#check_api_layers` without arguments checks every tagged declaration in the environment.
`#check_api_layers a b` checks only the named declarations (used by the negative test).

`#check_api_instances` checks globally registered library instances of `Repr`, `DecidableEq`,
`Inhabited` whose target has a tagged inductive type as its head. Such instances must carry a
layer tag. It inspects instance types rather than declaration names.

`#check_api_umbrella` verifies that every tagged declaration is defined in a module that the
umbrella module `NPComplete` imports (transitively). Only the umbrella is promised to clients
as an entry point, so a tagged declaration reachable only through another module would be a
public promise that `import NPComplete` does not deliver. A declaration of the module being
elaborated is never in the closure, because no module imports the module under elaboration.
`#check_api_umbrella a b` checks only the named declarations (used by the negative test).
-/

open Lean Elab Command Meta

public meta section

namespace NPComplete.ApiLayer

inductive Layer where
  | stable
  | construction
  deriving BEq, Inhabited

def Layer.toString : Layer → String
  | .stable => "stable_api"
  | .construction => "construction_api"

/-- All declarations carrying `attr`, in imported modules and in the current module. -/
def taggedNames (attr : TagAttribute) (env : Environment) : Array Name := Id.run do
  let mut r : Array Name := #[]
  for i in [0:env.header.moduleNames.size] do
    r := r ++ attr.ext.getModuleEntries env i
  for n in attr.ext.getState env do
    r := r.push n
  return r

def layerOf (env : Environment) (n : Name) : Option Layer :=
  if stableApiAttr.hasTag env n then some .stable
  else if constructionApiAttr.hasTag env n then some .construction
  else none

/-- Name components that mark an auxiliary declaration generated for an inductive type. -/
def auxComponents : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "noConfusion",
    "noConfusionType", "ctorElim", "ctorElimType", "ctorIdx", "sizeOf_spec", "inj", "injEq"]

/-- Cut `n` back to the part before its first auxiliary component. -/
def stripAux (n : Name) : Name :=
  let comps := n.components
  let kept := comps.takeWhile fun c => !(auxComponents.contains c.toString)
  kept.foldl (fun acc c => acc ++ c) Name.anonymous

partial def stripInternal (n : Name) : Name :=
  if isPrivateName n then n
  else if n.isInternalDetail then stripInternal n.getPrefix
  else n

def layerCheckName (n : Name) : Name :=
  if isPrivateName n then (privateToUserName? n).getD n else n

/-- The declaration a constant occurring in a statement is accounted to. -/
partial def owner (env : Environment) (c : Name) : Name :=
  let c := stripAux (stripInternal c)
  match env.find? c with
  | some (.ctorInfo i) => i.induct
  | some (.recInfo i) => i.getMajorInduct
  | _ =>
    match env.getProjectionFnInfo? c with
    | some pi => match env.find? pi.ctorName with
      | some (.ctorInfo i) => i.induct
      | _ => c
    | none =>
      if Meta.isMatcherCore env c then owner env c.getPrefix else c

def endsInSort : Expr → Bool
  | .forallE _ _ b _ => endsInSort b
  | .sort _ => true
  | _ => false

/-- The expressions that make up the statement of `n`, labelled by where they come from. -/
def statementParts (env : Environment) (n : Name) : Array (String × Expr) := Id.run do
  let some ci := env.find? n | return #[]
  let mut parts : Array (String × Expr) := #[("type", ci.type)]
  match ci with
  | .defnInfo d => if endsInSort d.type then parts := parts.push ("body", d.value)
  | .inductInfo i =>
    for c in i.ctors do
      if let some cc := env.find? c then parts := parts.push (s!"constructor `{c}`", cc.type)
  | _ => pure ()
  return parts

/-- The value of an auxiliary definition generated for `n` itself (`n._f`, `n._mutual`, matchers
of `n`), which holds the real body of a definition compiled by structural recursion. -/
def auxBody? (env : Environment) (n c : Name) : Option Expr :=
  if c != n && c.isInternalDetail && !isPrivateName c && stripInternal c == n then
    match env.find? c with
    | some (.defnInfo d) => some d.value
    | _ => none
  else none

def allowed (env : Environment) (l : Layer) (d : Name) : Bool :=
  match layerOf env d, l with
  | some .stable, _ => true
  | some .construction, .construction => true
  | _, _ => false

/-- Violations of the layering for the tagged declaration `n`. -/
partial def violationsOf (env : Environment) (n : Name) : Array String := Id.run do
  let some l := layerOf env n | return #[s!"`{layerCheckName n}` is not tagged"]
  let mut out : Array String := #[]
  if stableApiAttr.hasTag env n && constructionApiAttr.hasTag env n then
    out := out.push s!"`{layerCheckName n}` carries both stable_api and construction_api"
  if let some ci := env.find? n then
    if let .axiomInfo _ := ci then
      if endsInSort ci.type then
        out := out.push s!"`{layerCheckName n}` has a body that is not visible here, so its statement \
          cannot be inspected; mark it `@[expose]` or check it with `import all`"
  let mut seen : NameSet := {}
  let mut visited : NameSet := {}
  let mut work : Array (String × Expr) := (statementParts env n).reverse
  while !work.isEmpty do
    let (where_, e) := work.back!
    work := work.pop
    for c in e.getUsedConstants do
      if (layerCheckName c).getRoot != `NPComplete then continue
      if let some b := auxBody? env n c then
        unless visited.contains c do
          visited := visited.insert c
          work := work.push (where_, b)
        continue
      let d := owner env c
      let displayD := layerCheckName d
      if displayD == layerCheckName n || displayD.getRoot != `NPComplete || seen.contains d then continue
      seen := seen.insert d
      unless allowed env l d do
        let have_ := match layerOf env d with
          | some l' => l'.toString
          | none => "untagged"
        out := out.push
          s!"{l.toString} declaration `{layerCheckName n}` mentions {have_} `{displayD}` in its {where_}"
  return out

/-- Remove instance parameters to inspect the class application at its result. -/
partial def instanceResult : Expr → Expr
  | .forallE _ _ b _ => instanceResult b
  | .mdata _ b => instanceResult b
  | e => e

/-- Recognize a tracked class applied to a tagged inductive or structure. -/
def publicInstanceTarget? (env : Environment) (type : Expr) : Option Name := do
  let e := instanceResult type
  let cls ← e.getAppFn.constName?
  guard (cls == ``Repr || cls == ``DecidableEq || cls == ``Inhabited)
  let arg ← e.getAppArgs[0]?
  let n ← arg.getAppFn.constName?
  guard ((layerOf env n).isSome)
  let .inductInfo _ ← env.find? n | none
  return n

syntax (name := checkApiInstances) "#check_api_instances" : command

@[command_elab checkApiInstances] def elabCheckApiInstances : CommandElab := fun stx => do
  let env ← getEnv
  let names := (env.constants.toList.map Prod.fst |>.filter fun n =>
    (layerCheckName n).getRoot == `NPComplete).toArray.qsort Name.lt
  for n in names do
    let some ci := env.find? n | continue
    let some target := publicInstanceTarget? env ci.type | continue
    let some entry := (instanceExtension.getState env).instanceNames.find? n | continue
    unless entry.attrKind matches .global do continue
    if (layerOf env n).isNone then
      logErrorAt stx s!"instance `{layerCheckName n}` for public type `{target}` is untagged"

syntax (name := checkApiLayers) "#check_api_layers" (ppSpace ident)* : command

@[command_elab checkApiLayers] def elabCheckApiLayers : CommandElab := fun stx => do
  let env ← getEnv
  let names ← match stx[1].getArgs.toList with
    | [] => pure ((taggedNames stableApiAttr env ++ taggedNames constructionApiAttr env).qsort
        Name.lt)
    | ids => ids.toArray.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  for n in names do
    for v in violationsOf env n do
      logErrorAt stx v

/-- The root of the import closure that clients are promised. -/
def umbrellaModule : Name := `NPComplete

/-- All modules that `root` imports, directly or transitively, including `root` itself. -/
partial def importClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut idx : Std.HashMap Name Nat := {}
  for h : i in [0:env.header.moduleNames.size] do
    idx := idx.insert env.header.moduleNames[i] i
  let mut seen : NameSet := {}
  let mut work : Array Name := #[root]
  while !work.isEmpty do
    let m := work.back!
    work := work.pop
    if seen.contains m then continue
    seen := seen.insert m
    if let some i := idx[m]? then
      for imp in env.header.moduleData[i]!.imports do
        work := work.push imp.module
  return seen

/-- Modules of `NPComplete` in the import closure of `root` that are not loaded in `env`: their
tagged declarations are invisible to the checks, because a non-public import is not loaded by an
importer of the importing module. -/
def unloadedModules (env : Environment) (closure : NameSet) : Array Name :=
  (closure.toList.filter fun m =>
    m.getRoot == `NPComplete && !env.header.moduleNames.contains m).toArray.qsort Name.lt

/-- The module defining `n`; the module being elaborated for a declaration not yet imported. -/
def definingModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i]!
  | none => env.mainModule

/-- Violations of the umbrella requirement for the tagged declaration `n`. -/
def umbrellaViolationsOf (env : Environment) (closure : NameSet) (n : Name) : Array String :=
  let m := definingModule env n
  if closure.contains m then #[]
  else #[s!"tagged declaration `{layerCheckName n}` is defined in `{m}`, which `{umbrellaModule}` does not import"]

syntax (name := checkApiUmbrella) "#check_api_umbrella" (ppSpace ident)* : command

@[command_elab checkApiUmbrella] def elabCheckApiUmbrella : CommandElab := fun stx => do
  let env ← getEnv
  let closure := importClosure env umbrellaModule
  unless env.header.moduleNames.contains umbrellaModule do
    logErrorAt stx s!"module `{umbrellaModule}` is not imported, so its closure is unknown"
    return
  let names ← match stx[1].getArgs.toList with
    | [] => pure ((taggedNames stableApiAttr env ++ taggedNames constructionApiAttr env).qsort
        Name.lt)
    | ids => ids.toArray.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  for m in unloadedModules env closure do
    logErrorAt stx s!"module `{m}` is in the closure of `{umbrellaModule}` but not loaded here, \
      so its tagged declarations are not checked; import it or use `public import`"
  for n in names do
    for v in umbrellaViolationsOf env closure n do
      logErrorAt stx v

end NPComplete.ApiLayer
