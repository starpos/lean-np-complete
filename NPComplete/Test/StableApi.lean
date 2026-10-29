module

public import NPComplete

/-!
# Pins of the stable API

Every `stable_api` declaration appears here with its statement. `#check @X` pins the type; for a
structure, an inductive type or a definition whose value is itself the statement (a predicate or
a type), and for a few small encodings, `#print X` pins the definition as well. A change to any of
these fails the build of this module, so changing a stable declaration forces an intentional edit
of the expected output below, which is the review point for a breaking change.

Construction API declarations are deliberately not pinned: they are allowed to change.
-/

/--
info: NPComplete.BitEncoding.Bits : Type
-/
#guard_msgs in
#check @NPComplete.BitEncoding.Bits

/--
info: @[reducible, expose] def NPComplete.BitEncoding.Bits : Type :=
List Bool
-/
#guard_msgs in
#print NPComplete.BitEncoding.Bits

/--
info: NPComplete.BitEncoding.encodeBool : Bool → NPComplete.BitEncoding.Bits
-/
#guard_msgs in
#check @NPComplete.BitEncoding.encodeBool

/--
info: @[expose] def NPComplete.BitEncoding.encodeBool : Bool → NPComplete.BitEncoding.Bits :=
fun b => [b]
-/
#guard_msgs in
#print NPComplete.BitEncoding.encodeBool

/--
info: NPComplete.BitEncoding.encodeBool_injective : Function.Injective NPComplete.BitEncoding.encodeBool
-/
#guard_msgs in
#check @NPComplete.BitEncoding.encodeBool_injective

/--
info: @NPComplete.BitEncoding.encodeList : {α : Type u_1} →
  (α → NPComplete.BitEncoding.Bits) → List α → NPComplete.BitEncoding.Bits
-/
#guard_msgs in
#check @NPComplete.BitEncoding.encodeList

/--
info: @[expose] def NPComplete.BitEncoding.encodeList.{u_1} : {α : Type u_1} →
  (α → NPComplete.BitEncoding.Bits) → List α → NPComplete.BitEncoding.Bits :=
fun {α} enc l => NPComplete.BitEncoding.encodeNat l.length ++ (List.map enc l).flatten
-/
#guard_msgs in
#print NPComplete.BitEncoding.encodeList

/--
info: @NPComplete.BitEncoding.encodeList_injective : ∀ {α : Type u_1} {enc : α → NPComplete.BitEncoding.Bits},
  (∀ {x y : α} {p q : NPComplete.BitEncoding.Bits}, enc x ++ p = enc y ++ q → x = y ∧ p = q) →
    Function.Injective (NPComplete.BitEncoding.encodeList enc)
-/
#guard_msgs in
#check @NPComplete.BitEncoding.encodeList_injective

/--
info: NPComplete.BitEncoding.encodeNat : ℕ → NPComplete.BitEncoding.Bits
-/
#guard_msgs in
#check @NPComplete.BitEncoding.encodeNat

/--
info: NPComplete.BitEncoding.encodeNat_injective : Function.Injective NPComplete.BitEncoding.encodeNat
-/
#guard_msgs in
#check @NPComplete.BitEncoding.encodeNat_injective

/--
info: NPComplete.BitEncoding.encodeNat_length : ∀ (n : ℕ), List.length (NPComplete.BitEncoding.encodeNat n) = n + 1
-/
#guard_msgs in
#check @NPComplete.BitEncoding.encodeNat_length

/--
info: NPComplete.BitEncoding.encodeNat_succ : ∀ (n : ℕ),
  NPComplete.BitEncoding.encodeNat (n + 1) = false :: NPComplete.BitEncoding.encodeNat n
-/
#guard_msgs in
#check @NPComplete.BitEncoding.encodeNat_succ

/--
info: NPComplete.BitEncoding.encodeNat_zero : NPComplete.BitEncoding.encodeNat 0 = [true]
-/
#guard_msgs in
#check @NPComplete.BitEncoding.encodeNat_zero

/--
info: NPComplete.BoundedWhile.Expr : Type
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr

/--
info: inductive NPComplete.BoundedWhile.Expr : Type
number of parameters: 0
constructors:
NPComplete.BoundedWhile.Expr.const : ℕ → NPComplete.BoundedWhile.Expr
NPComplete.BoundedWhile.Expr.reg : ℕ → NPComplete.BoundedWhile.Expr
NPComplete.BoundedWhile.Expr.regInd : NPComplete.BoundedWhile.Expr → NPComplete.BoundedWhile.Expr
NPComplete.BoundedWhile.Expr.add : NPComplete.BoundedWhile.Expr →
  NPComplete.BoundedWhile.Expr → NPComplete.BoundedWhile.Expr
NPComplete.BoundedWhile.Expr.sub : NPComplete.BoundedWhile.Expr →
  NPComplete.BoundedWhile.Expr → NPComplete.BoundedWhile.Expr
NPComplete.BoundedWhile.Expr.mul : NPComplete.BoundedWhile.Expr →
  NPComplete.BoundedWhile.Expr → NPComplete.BoundedWhile.Expr
NPComplete.BoundedWhile.Expr.lt : NPComplete.BoundedWhile.Expr →
  NPComplete.BoundedWhile.Expr → NPComplete.BoundedWhile.Expr
NPComplete.BoundedWhile.Expr.eq : NPComplete.BoundedWhile.Expr →
  NPComplete.BoundedWhile.Expr → NPComplete.BoundedWhile.Expr
-/
#guard_msgs in
#print NPComplete.BoundedWhile.Expr

/--
info: NPComplete.BoundedWhile.Expr.cost : NPComplete.BoundedWhile.Expr → ℕ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.cost

/--
info: NPComplete.BoundedWhile.Expr.cost_const : ∀ (n : ℕ), (NPComplete.BoundedWhile.Expr.const n).cost = 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.cost_const

/--
info: NPComplete.BoundedWhile.Expr.cost_reg : ∀ (r : ℕ), (NPComplete.BoundedWhile.Expr.reg r).cost = 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.cost_reg

/--
info: NPComplete.BoundedWhile.Expr.cost_regInd : ∀ (e : NPComplete.BoundedWhile.Expr), e.regInd.cost = e.cost + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.cost_regInd

/--
info: NPComplete.BoundedWhile.Expr.cost_add : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr),
  (e₁.add e₂).cost = e₁.cost + e₂.cost + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.cost_add

/--
info: NPComplete.BoundedWhile.Expr.cost_sub : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr),
  (e₁.sub e₂).cost = e₁.cost + e₂.cost + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.cost_sub

/--
info: NPComplete.BoundedWhile.Expr.cost_mul : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr),
  (e₁.mul e₂).cost = e₁.cost + e₂.cost + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.cost_mul

/--
info: NPComplete.BoundedWhile.Expr.cost_lt : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr), (e₁.lt e₂).cost = e₁.cost + e₂.cost + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.cost_lt

/--
info: NPComplete.BoundedWhile.Expr.cost_eq : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr), (e₁.eq e₂).cost = e₁.cost + e₂.cost + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.cost_eq

/--
info: NPComplete.BoundedWhile.Expr.eval : NPComplete.BoundedWhile.Expr → NPComplete.BoundedWhile.Store → ℕ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.eval

/--
info: NPComplete.BoundedWhile.Expr.eval_const : ∀ (n : ℕ) (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Expr.const n).eval σ = n
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.eval_const

/--
info: NPComplete.BoundedWhile.Expr.eval_reg : ∀ (r : ℕ) (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Expr.reg r).eval σ = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.eval_reg

/--
info: NPComplete.BoundedWhile.Expr.eval_regInd : ∀ (e : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  e.regInd.eval σ = σ (e.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.eval_regInd

/--
info: NPComplete.BoundedWhile.Expr.eval_add : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  (e₁.add e₂).eval σ = e₁.eval σ + e₂.eval σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.eval_add

/--
info: NPComplete.BoundedWhile.Expr.eval_sub : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  (e₁.sub e₂).eval σ = e₁.eval σ - e₂.eval σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.eval_sub

/--
info: NPComplete.BoundedWhile.Expr.eval_mul : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  (e₁.mul e₂).eval σ = e₁.eval σ * e₂.eval σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.eval_mul

/--
info: NPComplete.BoundedWhile.Expr.eval_lt : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  (e₁.lt e₂).eval σ = if e₁.eval σ < e₂.eval σ then 1 else 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.eval_lt

/--
info: NPComplete.BoundedWhile.Expr.eval_eq : ∀ (e₁ e₂ : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  (e₁.eq e₂).eval σ = if e₁.eval σ = e₂.eval σ then 1 else 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.eval_eq

/--
info: NPComplete.BoundedWhile.Expr.lb : NPComplete.BoundedWhile.Expr → ℕ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb

/--
info: NPComplete.BoundedWhile.Expr.lb_const : ∀ (n : ℕ), (NPComplete.BoundedWhile.Expr.const n).lb = n
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb_const

/--
info: NPComplete.BoundedWhile.Expr.lb_reg : ∀ (r : ℕ), (NPComplete.BoundedWhile.Expr.reg r).lb = 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb_reg

/--
info: NPComplete.BoundedWhile.Expr.lb_regInd : ∀ (e : NPComplete.BoundedWhile.Expr), e.regInd.lb = 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb_regInd

/--
info: NPComplete.BoundedWhile.Expr.lb_add : ∀ (a b : NPComplete.BoundedWhile.Expr), (a.add b).lb = a.lb + b.lb
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb_add

/--
info: NPComplete.BoundedWhile.Expr.lb_sub : ∀ (a b : NPComplete.BoundedWhile.Expr), (a.sub b).lb = 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb_sub

/--
info: NPComplete.BoundedWhile.Expr.lb_mul : ∀ (a b : NPComplete.BoundedWhile.Expr), (a.mul b).lb = a.lb * b.lb
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb_mul

/--
info: NPComplete.BoundedWhile.Expr.lb_lt : ∀ (a b : NPComplete.BoundedWhile.Expr), (a.lt b).lb = 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb_lt

/--
info: NPComplete.BoundedWhile.Expr.lb_eq : ∀ (a b : NPComplete.BoundedWhile.Expr), (a.eq b).lb = 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb_eq

/--
info: NPComplete.BoundedWhile.Expr.lb_le : ∀ (e : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  e.lb ≤ e.eval σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Expr.lb_le

/--
info: NPComplete.BoundedWhile.Program : Type
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program

/--
info: inductive NPComplete.BoundedWhile.Program : Type
number of parameters: 0
constructors:
NPComplete.BoundedWhile.Program.skip : NPComplete.BoundedWhile.Program
NPComplete.BoundedWhile.Program.assign : ℕ → NPComplete.BoundedWhile.Expr → NPComplete.BoundedWhile.Program
NPComplete.BoundedWhile.Program.assignInd : NPComplete.BoundedWhile.Expr →
  NPComplete.BoundedWhile.Expr → NPComplete.BoundedWhile.Program
NPComplete.BoundedWhile.Program.seq : NPComplete.BoundedWhile.Program →
  NPComplete.BoundedWhile.Program → NPComplete.BoundedWhile.Program
NPComplete.BoundedWhile.Program.ifNZ : NPComplete.BoundedWhile.Expr →
  NPComplete.BoundedWhile.Program → NPComplete.BoundedWhile.Program → NPComplete.BoundedWhile.Program
NPComplete.BoundedWhile.Program.forN : NPComplete.BoundedWhile.Expr →
  NPComplete.BoundedWhile.Program → NPComplete.BoundedWhile.Program
NPComplete.BoundedWhile.Program.scanList : List ℕ →
  ℕ → NPComplete.BoundedWhile.Program → NPComplete.BoundedWhile.Program
NPComplete.BoundedWhile.Program.lookup : List (ℕ × ℕ) → ℕ → ℕ → NPComplete.BoundedWhile.Program
-/
#guard_msgs in
#print NPComplete.BoundedWhile.Program

/--
info: NPComplete.BoundedWhile.Program.Avoids : (ℕ → Prop) → NPComplete.BoundedWhile.Program → Prop
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.Avoids

/--
info: @[expose] def NPComplete.BoundedWhile.Program.Avoids : (ℕ → Prop) → NPComplete.BoundedWhile.Program → Prop :=
fun P x => NPComplete.BoundedWhile.Program.brecOn x (NPComplete.BoundedWhile.Program.Avoids._f P)
-/
#guard_msgs in
#print NPComplete.BoundedWhile.Program.Avoids

/--
info: NPComplete.BoundedWhile.Program.avoids_skip : ∀ (P : ℕ → Prop),
  NPComplete.BoundedWhile.Program.Avoids P NPComplete.BoundedWhile.Program.skip ↔ True
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoids_skip

/--
info: NPComplete.BoundedWhile.Program.avoids_assign : ∀ (P : ℕ → Prop) (r : ℕ) (e : NPComplete.BoundedWhile.Expr),
  NPComplete.BoundedWhile.Program.Avoids P (NPComplete.BoundedWhile.Program.assign r e) ↔ ¬P r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoids_assign

/--
info: NPComplete.BoundedWhile.Program.avoids_assignInd : ∀ (P : ℕ → Prop) (eA e : NPComplete.BoundedWhile.Expr),
  NPComplete.BoundedWhile.Program.Avoids P (NPComplete.BoundedWhile.Program.assignInd eA e) ↔ False
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoids_assignInd

/--
info: NPComplete.BoundedWhile.Program.avoids_seq : ∀ (P : ℕ → Prop) (p q : NPComplete.BoundedWhile.Program),
  NPComplete.BoundedWhile.Program.Avoids P (p.seq q) ↔
    NPComplete.BoundedWhile.Program.Avoids P p ∧ NPComplete.BoundedWhile.Program.Avoids P q
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoids_seq

/--
info: NPComplete.BoundedWhile.Program.avoids_ifNZ : ∀ (P : ℕ → Prop) (c : NPComplete.BoundedWhile.Expr)
  (t f : NPComplete.BoundedWhile.Program),
  NPComplete.BoundedWhile.Program.Avoids P (NPComplete.BoundedWhile.Program.ifNZ c t f) ↔
    NPComplete.BoundedWhile.Program.Avoids P t ∧ NPComplete.BoundedWhile.Program.Avoids P f
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoids_ifNZ

/--
info: NPComplete.BoundedWhile.Program.avoids_forN : ∀ (P : ℕ → Prop) (n : NPComplete.BoundedWhile.Expr)
  (b : NPComplete.BoundedWhile.Program),
  NPComplete.BoundedWhile.Program.Avoids P (NPComplete.BoundedWhile.Program.forN n b) ↔
    NPComplete.BoundedWhile.Program.Avoids P b
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoids_forN

/--
info: NPComplete.BoundedWhile.Program.avoids_scanList : ∀ (P : ℕ → Prop) (xs : List ℕ) (r : ℕ)
  (b : NPComplete.BoundedWhile.Program),
  NPComplete.BoundedWhile.Program.Avoids P (NPComplete.BoundedWhile.Program.scanList xs r b) ↔
    ¬P r ∧ NPComplete.BoundedWhile.Program.Avoids P b
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoids_scanList

/--
info: NPComplete.BoundedWhile.Program.avoids_lookup : ∀ (P : ℕ → Prop) (pairs : List (ℕ × ℕ)) (k v : ℕ),
  NPComplete.BoundedWhile.Program.Avoids P (NPComplete.BoundedWhile.Program.lookup pairs k v) ↔ ¬P v
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoids_lookup

/--
info: @NPComplete.BoundedWhile.Program.Avoids.avoidsAbove : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop},
  NPComplete.BoundedWhile.Program.Avoids P p → ∀ (B : ℕ), NPComplete.BoundedWhile.Program.AvoidsAbove P B p
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.Avoids.avoidsAbove

/--
info: NPComplete.BoundedWhile.Program.Avoids.decidable : (P : ℕ → Prop) →
  [DecidablePred P] → (p : NPComplete.BoundedWhile.Program) → Decidable (NPComplete.BoundedWhile.Program.Avoids P p)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.Avoids.decidable

/--
info: @NPComplete.BoundedWhile.Program.Avoids.eval_frame : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop},
  NPComplete.BoundedWhile.Program.Avoids P p → ∀ (σ : NPComplete.BoundedWhile.Store) {r : ℕ}, P r → p.eval σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.Avoids.eval_frame

/--
info: @NPComplete.BoundedWhile.Program.Avoids.loopEval_frame : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop},
  NPComplete.BoundedWhile.Program.Avoids P p →
    ∀ {r : ℕ}, P r → ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.loopEval p k σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.Avoids.loopEval_frame

/--
info: @NPComplete.BoundedWhile.Program.Avoids.mono : ∀ {p : NPComplete.BoundedWhile.Program} {P Q : ℕ → Prop},
  NPComplete.BoundedWhile.Program.Avoids P p → (∀ (r : ℕ), Q r → P r) → NPComplete.BoundedWhile.Program.Avoids Q p
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.Avoids.mono

/--
info: @NPComplete.BoundedWhile.Program.Avoids.preserves : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop}
  {Q : NPComplete.BoundedWhile.Store → Prop},
  NPComplete.BoundedWhile.Program.Avoids P p →
    NPComplete.BoundedWhile.ReadsOnly P Q → ∀ {σ : NPComplete.BoundedWhile.Store}, Q σ → Q (p.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.Avoids.preserves

/--
info: @NPComplete.BoundedWhile.Program.Avoids.writesAvoid : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop},
  NPComplete.BoundedWhile.Program.Avoids P p → p.WritesAvoid P
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.Avoids.writesAvoid

/--
info: NPComplete.BoundedWhile.Program.AvoidsAbove : (ℕ → Prop) → ℕ → NPComplete.BoundedWhile.Program → Prop
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.AvoidsAbove

/--
info: @[expose] def NPComplete.BoundedWhile.Program.AvoidsAbove : (ℕ → Prop) → ℕ → NPComplete.BoundedWhile.Program → Prop :=
fun P B x => NPComplete.BoundedWhile.Program.brecOn x (NPComplete.BoundedWhile.Program.AvoidsAbove._f P B)
-/
#guard_msgs in
#print NPComplete.BoundedWhile.Program.AvoidsAbove

/--
info: NPComplete.BoundedWhile.Program.avoidsAbove_skip : ∀ (P : ℕ → Prop) (B : ℕ),
  NPComplete.BoundedWhile.Program.AvoidsAbove P B NPComplete.BoundedWhile.Program.skip ↔ True
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoidsAbove_skip

/--
info: NPComplete.BoundedWhile.Program.avoidsAbove_assign : ∀ (P : ℕ → Prop) (B r : ℕ) (e : NPComplete.BoundedWhile.Expr),
  NPComplete.BoundedWhile.Program.AvoidsAbove P B (NPComplete.BoundedWhile.Program.assign r e) ↔ ¬P r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoidsAbove_assign

/--
info: NPComplete.BoundedWhile.Program.avoidsAbove_assignInd : ∀ (P : ℕ → Prop) (B : ℕ) (eA e : NPComplete.BoundedWhile.Expr),
  NPComplete.BoundedWhile.Program.AvoidsAbove P B (NPComplete.BoundedWhile.Program.assignInd eA e) ↔ B ≤ eA.lb
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoidsAbove_assignInd

/--
info: NPComplete.BoundedWhile.Program.avoidsAbove_seq : ∀ (P : ℕ → Prop) (B : ℕ) (p q : NPComplete.BoundedWhile.Program),
  NPComplete.BoundedWhile.Program.AvoidsAbove P B (p.seq q) ↔
    NPComplete.BoundedWhile.Program.AvoidsAbove P B p ∧ NPComplete.BoundedWhile.Program.AvoidsAbove P B q
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoidsAbove_seq

/--
info: NPComplete.BoundedWhile.Program.avoidsAbove_ifNZ : ∀ (P : ℕ → Prop) (B : ℕ) (c : NPComplete.BoundedWhile.Expr)
  (t f : NPComplete.BoundedWhile.Program),
  NPComplete.BoundedWhile.Program.AvoidsAbove P B (NPComplete.BoundedWhile.Program.ifNZ c t f) ↔
    NPComplete.BoundedWhile.Program.AvoidsAbove P B t ∧ NPComplete.BoundedWhile.Program.AvoidsAbove P B f
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoidsAbove_ifNZ

/--
info: NPComplete.BoundedWhile.Program.avoidsAbove_forN : ∀ (P : ℕ → Prop) (B : ℕ) (n : NPComplete.BoundedWhile.Expr)
  (b : NPComplete.BoundedWhile.Program),
  NPComplete.BoundedWhile.Program.AvoidsAbove P B (NPComplete.BoundedWhile.Program.forN n b) ↔
    NPComplete.BoundedWhile.Program.AvoidsAbove P B b
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoidsAbove_forN

/--
info: NPComplete.BoundedWhile.Program.avoidsAbove_scanList : ∀ (P : ℕ → Prop) (B : ℕ) (xs : List ℕ) (r : ℕ)
  (b : NPComplete.BoundedWhile.Program),
  NPComplete.BoundedWhile.Program.AvoidsAbove P B (NPComplete.BoundedWhile.Program.scanList xs r b) ↔
    ¬P r ∧ NPComplete.BoundedWhile.Program.AvoidsAbove P B b
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoidsAbove_scanList

/--
info: NPComplete.BoundedWhile.Program.avoidsAbove_lookup : ∀ (P : ℕ → Prop) (B : ℕ) (pairs : List (ℕ × ℕ)) (k v : ℕ),
  NPComplete.BoundedWhile.Program.AvoidsAbove P B (NPComplete.BoundedWhile.Program.lookup pairs k v) ↔ ¬P v
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.avoidsAbove_lookup

/--
info: NPComplete.BoundedWhile.Program.AvoidsAbove.decidable : (P : ℕ → Prop) →
  [DecidablePred P] →
    (B : ℕ) → (p : NPComplete.BoundedWhile.Program) → Decidable (NPComplete.BoundedWhile.Program.AvoidsAbove P B p)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.AvoidsAbove.decidable

/--
info: @NPComplete.BoundedWhile.Program.AvoidsAbove.eval_frame : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop}
  {B : ℕ},
  NPComplete.BoundedWhile.Program.AvoidsAbove P B p →
    ∀ (σ : NPComplete.BoundedWhile.Store) {r : ℕ}, P r → r < B → p.eval σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.AvoidsAbove.eval_frame

/--
info: @NPComplete.BoundedWhile.Program.AvoidsAbove.loopEval_frame : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop}
  {B : ℕ},
  NPComplete.BoundedWhile.Program.AvoidsAbove P B p →
    ∀ {r : ℕ},
      P r → r < B → ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.loopEval p k σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.AvoidsAbove.loopEval_frame

/--
info: @NPComplete.BoundedWhile.Program.AvoidsAbove.mono : ∀ {p : NPComplete.BoundedWhile.Program} {P Q : ℕ → Prop} {B B' : ℕ},
  NPComplete.BoundedWhile.Program.AvoidsAbove P B p →
    (∀ (r : ℕ), Q r → P r) → B' ≤ B → NPComplete.BoundedWhile.Program.AvoidsAbove Q B' p
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.AvoidsAbove.mono

/--
info: @NPComplete.BoundedWhile.Program.AvoidsAbove.preserves : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop} {B : ℕ}
  {Q : NPComplete.BoundedWhile.Store → Prop},
  NPComplete.BoundedWhile.Program.AvoidsAbove P B p →
    NPComplete.BoundedWhile.ReadsOnly (fun r => P r ∧ r < B) Q →
      ∀ {σ : NPComplete.BoundedWhile.Store}, Q σ → Q (p.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.AvoidsAbove.preserves

/--
info: NPComplete.BoundedWhile.Program.WritesAvoid : NPComplete.BoundedWhile.Program → (ℕ → Prop) → Prop
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.WritesAvoid

/--
info: @[expose] def NPComplete.BoundedWhile.Program.WritesAvoid : NPComplete.BoundedWhile.Program → (ℕ → Prop) → Prop :=
fun p P => ∃ ws, p.directWrites = some ws ∧ ∀ w ∈ ws, ¬P w
-/
#guard_msgs in
#print NPComplete.BoundedWhile.Program.WritesAvoid

/--
info: @NPComplete.BoundedWhile.Program.WritesAvoid.eval_frame : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop},
  p.WritesAvoid P → ∀ (σ : NPComplete.BoundedWhile.Store) {r : ℕ}, P r → p.eval σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.WritesAvoid.eval_frame

/--
info: @NPComplete.BoundedWhile.Program.WritesAvoid.loopEval_frame : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop},
  p.WritesAvoid P →
    ∀ {r : ℕ}, P r → ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.loopEval p k σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.WritesAvoid.loopEval_frame

/--
info: @NPComplete.BoundedWhile.Program.WritesAvoid.mono : ∀ {p : NPComplete.BoundedWhile.Program} {P Q : ℕ → Prop},
  p.WritesAvoid P → (∀ (r : ℕ), Q r → P r) → p.WritesAvoid Q
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.WritesAvoid.mono

/--
info: @NPComplete.BoundedWhile.Program.WritesAvoid.preserves : ∀ {p : NPComplete.BoundedWhile.Program} {P : ℕ → Prop}
  {Q : NPComplete.BoundedWhile.Store → Prop},
  p.WritesAvoid P → NPComplete.BoundedWhile.ReadsOnly P Q → ∀ {σ : NPComplete.BoundedWhile.Store}, Q σ → Q (p.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.WritesAvoid.preserves

/--
info: NPComplete.BoundedWhile.Program.cost : NPComplete.BoundedWhile.Program → NPComplete.BoundedWhile.Store → ℕ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.cost

/--
info: NPComplete.BoundedWhile.Program.directWrites : NPComplete.BoundedWhile.Program → Option (List ℕ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.directWrites

/--
info: NPComplete.BoundedWhile.Program.directWrites_skip : NPComplete.BoundedWhile.Program.skip.directWrites = some []
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.directWrites_skip

/--
info: NPComplete.BoundedWhile.Program.directWrites_assign : ∀ (r : ℕ) (e : NPComplete.BoundedWhile.Expr),
  (NPComplete.BoundedWhile.Program.assign r e).directWrites = some [r]
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.directWrites_assign

/--
info: NPComplete.BoundedWhile.Program.directWrites_assignInd : ∀ (eA e : NPComplete.BoundedWhile.Expr),
  (NPComplete.BoundedWhile.Program.assignInd eA e).directWrites = none
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.directWrites_assignInd

/--
info: NPComplete.BoundedWhile.Program.directWrites_seq : ∀ (p q : NPComplete.BoundedWhile.Program),
  (p.seq q).directWrites = p.directWrites.bind fun a => Option.map (fun x => a ++ x) q.directWrites
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.directWrites_seq

/--
info: NPComplete.BoundedWhile.Program.directWrites_ifNZ : ∀ (c : NPComplete.BoundedWhile.Expr)
  (t f : NPComplete.BoundedWhile.Program),
  (NPComplete.BoundedWhile.Program.ifNZ c t f).directWrites =
    t.directWrites.bind fun a => Option.map (fun x => a ++ x) f.directWrites
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.directWrites_ifNZ

/--
info: NPComplete.BoundedWhile.Program.directWrites_forN : ∀ (n : NPComplete.BoundedWhile.Expr)
  (b : NPComplete.BoundedWhile.Program), (NPComplete.BoundedWhile.Program.forN n b).directWrites = b.directWrites
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.directWrites_forN

/--
info: NPComplete.BoundedWhile.Program.directWrites_scanList : ∀ (xs : List ℕ) (r : ℕ) (b : NPComplete.BoundedWhile.Program),
  (NPComplete.BoundedWhile.Program.scanList xs r b).directWrites = Option.map (fun x => r :: x) b.directWrites
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.directWrites_scanList

/--
info: NPComplete.BoundedWhile.Program.directWrites_lookup : ∀ (pairs : List (ℕ × ℕ)) (k v : ℕ),
  (NPComplete.BoundedWhile.Program.lookup pairs k v).directWrites = some [v]
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.directWrites_lookup

/--
info: NPComplete.BoundedWhile.Program.eval : NPComplete.BoundedWhile.Program →
  NPComplete.BoundedWhile.Store → NPComplete.BoundedWhile.Store
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.eval

/--
info: NPComplete.BoundedWhile.Program.eval_frame : ∀ (p : NPComplete.BoundedWhile.Program) (ws : List ℕ),
  p.directWrites = some ws → ∀ (σ : NPComplete.BoundedWhile.Store), ∀ r ∉ ws, p.eval σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.eval_frame

/--
info: @NPComplete.BoundedWhile.Program.eval_frame_of_ge : ∀ {p : NPComplete.BoundedWhile.Program} {ws : List ℕ} {B : ℕ},
  p.directWrites = some ws → (∀ w ∈ ws, B ≤ w) → ∀ (σ : NPComplete.BoundedWhile.Store) {r : ℕ}, r < B → p.eval σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.eval_frame_of_ge

/--
info: @NPComplete.BoundedWhile.Program.eval_frame_of_le : ∀ {p : NPComplete.BoundedWhile.Program} {ws : List ℕ} {B : ℕ},
  p.directWrites = some ws → (∀ w ∈ ws, w ≤ B) → ∀ (σ : NPComplete.BoundedWhile.Store) {r : ℕ}, B < r → p.eval σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.eval_frame_of_le

/--
info: @NPComplete.BoundedWhile.Program.eval_frame_of_pred : ∀ {p : NPComplete.BoundedWhile.Program} {ws : List ℕ}
  {P : ℕ → Prop},
  p.directWrites = some ws → (∀ w ∈ ws, ¬P w) → ∀ (σ : NPComplete.BoundedWhile.Store) {r : ℕ}, P r → p.eval σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Program.eval_frame_of_pred

/--
info: NPComplete.BoundedWhile.ReadsOnly : (ℕ → Prop) → (NPComplete.BoundedWhile.Store → Prop) → Prop
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.ReadsOnly

/--
info: @[expose] def NPComplete.BoundedWhile.ReadsOnly : (ℕ → Prop) → (NPComplete.BoundedWhile.Store → Prop) → Prop :=
fun P Q => ∀ (σ σ' : NPComplete.BoundedWhile.Store), (∀ (r : ℕ), P r → σ' r = σ r) → Q σ → Q σ'
-/
#guard_msgs in
#print NPComplete.BoundedWhile.ReadsOnly

/--
info: @NPComplete.BoundedWhile.ReadsOnly.mono : ∀ {P P' : ℕ → Prop} {Q : NPComplete.BoundedWhile.Store → Prop},
  (∀ (r : ℕ), P r → P' r) → NPComplete.BoundedWhile.ReadsOnly P Q → NPComplete.BoundedWhile.ReadsOnly P' Q
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.ReadsOnly.mono

/--
info: @NPComplete.BoundedWhile.ReadsOnly.of_lt : ∀ {P : ℕ → Prop} {Q : NPComplete.BoundedWhile.Store → Prop} {B : ℕ},
  (∀ (r : ℕ), P r → r < B) →
    NPComplete.BoundedWhile.ReadsOnly P Q → NPComplete.BoundedWhile.ReadsOnly (fun r => P r ∧ r < B) Q
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.ReadsOnly.of_lt

/--
info: NPComplete.BoundedWhile.Store : Type
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.Store

/--
info: @[expose] def NPComplete.BoundedWhile.Store : Type :=
ℕ → ℕ
-/
#guard_msgs in
#print NPComplete.BoundedWhile.Store

/--
info: NPComplete.BoundedWhile.cost_assign : ∀ (r : ℕ) (e : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.assign r e).cost σ = e.cost + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_assign

/--
info: NPComplete.BoundedWhile.cost_assignInd : ∀ (eA eV : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.assignInd eA eV).cost σ = eA.cost + eV.cost + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_assignInd

/--
info: NPComplete.BoundedWhile.cost_forN : ∀ (n : NPComplete.BoundedWhile.Expr) (body : NPComplete.BoundedWhile.Program)
  (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.forN n body).cost σ = n.cost + 1 + NPComplete.BoundedWhile.loopCost body (n.eval σ) σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_forN

/--
info: NPComplete.BoundedWhile.cost_forN_le_of_bounds : ∀ (n : NPComplete.BoundedWhile.Expr)
  (body : NPComplete.BoundedWhile.Program) (σ : NPComplete.BoundedWhile.Store) (B L : ℕ),
  (∀ (σ : NPComplete.BoundedWhile.Store), body.cost σ ≤ B) →
    n.eval σ ≤ L → (NPComplete.BoundedWhile.Program.forN n body).cost σ ≤ n.cost + 1 + L * B
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_forN_le_of_bounds

/--
info: NPComplete.BoundedWhile.cost_forN_le_of_inv : ∀ (n : NPComplete.BoundedWhile.Expr)
  (body : NPComplete.BoundedWhile.Program) (σ : NPComplete.BoundedWhile.Store)
  (P : NPComplete.BoundedWhile.Store → Prop) (B L : ℕ),
  P σ →
    (∀ (τ : NPComplete.BoundedWhile.Store), P τ → P (body.eval τ)) →
      (∀ (τ : NPComplete.BoundedWhile.Store), P τ → body.cost τ ≤ B) →
        n.eval σ ≤ L → (NPComplete.BoundedWhile.Program.forN n body).cost σ ≤ n.cost + 1 + L * B
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_forN_le_of_inv

/--
info: NPComplete.BoundedWhile.cost_ifNZ : ∀ (e : NPComplete.BoundedWhile.Expr) (t f : NPComplete.BoundedWhile.Program)
  (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.ifNZ e t f).cost σ = e.cost + 1 + if e.eval σ ≠ 0 then t.cost σ else f.cost σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_ifNZ

/--
info: NPComplete.BoundedWhile.cost_lookup : ∀ (pairs : List (ℕ × ℕ)) (kReg vReg : ℕ) (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.lookup pairs kReg vReg).cost σ = pairs.length + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_lookup

/--
info: NPComplete.BoundedWhile.cost_lookup_le_of_len : ∀ (pairs : List (ℕ × ℕ)) (kReg vReg : ℕ)
  (σ : NPComplete.BoundedWhile.Store) (L : ℕ),
  pairs.length ≤ L → (NPComplete.BoundedWhile.Program.lookup pairs kReg vReg).cost σ ≤ L + 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_lookup_le_of_len

/--
info: NPComplete.BoundedWhile.cost_scanList : ∀ (xs : List ℕ) (r : ℕ) (body : NPComplete.BoundedWhile.Program)
  (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.scanList xs r body).cost σ = 1 + NPComplete.BoundedWhile.scanListCost body xs r σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_scanList

/--
info: NPComplete.BoundedWhile.cost_scanList_le_of_bounds : ∀ (body : NPComplete.BoundedWhile.Program) (xs : List ℕ) (r : ℕ)
  (σ : NPComplete.BoundedWhile.Store) (B L : ℕ),
  (∀ (σ : NPComplete.BoundedWhile.Store), body.cost σ ≤ B) →
    xs.length ≤ L → (NPComplete.BoundedWhile.Program.scanList xs r body).cost σ ≤ 1 + L * B
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_scanList_le_of_bounds

/--
info: NPComplete.BoundedWhile.cost_seq : ∀ (p1 p2 : NPComplete.BoundedWhile.Program) (σ : NPComplete.BoundedWhile.Store),
  (p1.seq p2).cost σ = p1.cost σ + p2.cost (p1.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_seq

/--
info: NPComplete.BoundedWhile.cost_skip : ∀ (σ : NPComplete.BoundedWhile.Store),
  NPComplete.BoundedWhile.Program.skip.cost σ = 1
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.cost_skip

/--
info: NPComplete.BoundedWhile.emptyStore : NPComplete.BoundedWhile.Store
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.emptyStore

/--
info: NPComplete.BoundedWhile.eval_assign : ∀ (r : ℕ) (e : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.assign r e).eval σ = NPComplete.BoundedWhile.writeReg σ r (e.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.eval_assign

/--
info: NPComplete.BoundedWhile.eval_assignInd : ∀ (eA eV : NPComplete.BoundedWhile.Expr) (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.assignInd eA eV).eval σ = NPComplete.BoundedWhile.writeReg σ (eA.eval σ) (eV.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.eval_assignInd

/--
info: NPComplete.BoundedWhile.eval_forN : ∀ (n : NPComplete.BoundedWhile.Expr) (body : NPComplete.BoundedWhile.Program)
  (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.forN n body).eval σ = NPComplete.BoundedWhile.loopEval body (n.eval σ) σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.eval_forN

/--
info: NPComplete.BoundedWhile.eval_ifNZ : ∀ (e : NPComplete.BoundedWhile.Expr) (t f : NPComplete.BoundedWhile.Program)
  (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.ifNZ e t f).eval σ = if e.eval σ ≠ 0 then t.eval σ else f.eval σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.eval_ifNZ

/--
info: NPComplete.BoundedWhile.eval_lookup : ∀ (pairs : List (ℕ × ℕ)) (kReg vReg : ℕ) (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.lookup pairs kReg vReg).eval σ =
    NPComplete.BoundedWhile.writeReg σ vReg (NPComplete.BoundedWhile.findVal pairs (σ kReg))
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.eval_lookup

/--
info: NPComplete.BoundedWhile.eval_scanList : ∀ (xs : List ℕ) (r : ℕ) (body : NPComplete.BoundedWhile.Program)
  (σ : NPComplete.BoundedWhile.Store),
  (NPComplete.BoundedWhile.Program.scanList xs r body).eval σ = NPComplete.BoundedWhile.scanListEval body xs r σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.eval_scanList

/--
info: NPComplete.BoundedWhile.eval_seq : ∀ (p1 p2 : NPComplete.BoundedWhile.Program) (σ : NPComplete.BoundedWhile.Store),
  (p1.seq p2).eval σ = p2.eval (p1.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.eval_seq

/--
info: NPComplete.BoundedWhile.eval_skip : ∀ (σ : NPComplete.BoundedWhile.Store),
  NPComplete.BoundedWhile.Program.skip.eval σ = σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.eval_skip

/--
info: NPComplete.BoundedWhile.findVal : List (ℕ × ℕ) → ℕ → ℕ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.findVal

/--
info: NPComplete.BoundedWhile.findVal_cons : ∀ (k v key : ℕ) (rest : List (ℕ × ℕ)),
  NPComplete.BoundedWhile.findVal ((k, v) :: rest) key = if k = key then v else NPComplete.BoundedWhile.findVal rest key
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.findVal_cons

/--
info: NPComplete.BoundedWhile.findVal_nil : ∀ (key : ℕ), NPComplete.BoundedWhile.findVal [] key = 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.findVal_nil

/--
info: NPComplete.BoundedWhile.loopCost : NPComplete.BoundedWhile.Program → ℕ → NPComplete.BoundedWhile.Store → ℕ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopCost

/--
info: NPComplete.BoundedWhile.loopCost_le_of_body_le : ∀ (body : NPComplete.BoundedWhile.Program) (B : ℕ),
  (∀ (σ : NPComplete.BoundedWhile.Store), body.cost σ ≤ B) →
    ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.loopCost body k σ ≤ k * B
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopCost_le_of_body_le

/--
info: NPComplete.BoundedWhile.loopCost_le_of_body_le_inv : ∀ (body : NPComplete.BoundedWhile.Program)
  (P : NPComplete.BoundedWhile.Store → Prop) (B : ℕ),
  (∀ (σ : NPComplete.BoundedWhile.Store), P σ → P (body.eval σ)) →
    (∀ (σ : NPComplete.BoundedWhile.Store), P σ → body.cost σ ≤ B) →
      ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), P σ → NPComplete.BoundedWhile.loopCost body k σ ≤ k * B
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopCost_le_of_body_le_inv

/--
info: NPComplete.BoundedWhile.loopCost_succ : ∀ (body : NPComplete.BoundedWhile.Program) (k : ℕ)
  (σ : NPComplete.BoundedWhile.Store),
  NPComplete.BoundedWhile.loopCost body (k + 1) σ = body.cost σ + NPComplete.BoundedWhile.loopCost body k (body.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopCost_succ

/--
info: NPComplete.BoundedWhile.loopCost_zero : ∀ (body : NPComplete.BoundedWhile.Program) (σ : NPComplete.BoundedWhile.Store),
  NPComplete.BoundedWhile.loopCost body 0 σ = 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopCost_zero

/--
info: NPComplete.BoundedWhile.loopEval : NPComplete.BoundedWhile.Program →
  ℕ → NPComplete.BoundedWhile.Store → NPComplete.BoundedWhile.Store
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval

/--
info: NPComplete.BoundedWhile.loopEval_fixed : ∀ (b : NPComplete.BoundedWhile.Program) (σ : NPComplete.BoundedWhile.Store),
  b.eval σ = σ → ∀ (k : ℕ), NPComplete.BoundedWhile.loopEval b k σ = σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_fixed

/--
info: NPComplete.BoundedWhile.loopEval_frame : ∀ (b : NPComplete.BoundedWhile.Program) (r : ℕ),
  (∀ (σ : NPComplete.BoundedWhile.Store), b.eval σ r = σ r) →
    ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.loopEval b k σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_frame

/--
info: @NPComplete.BoundedWhile.loopEval_frame_of_ge : ∀ {b : NPComplete.BoundedWhile.Program} {ws : List ℕ} {B : ℕ},
  b.directWrites = some ws →
    (∀ w ∈ ws, B ≤ w) →
      ∀ {r : ℕ}, r < B → ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.loopEval b k σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_frame_of_ge

/--
info: @NPComplete.BoundedWhile.loopEval_frame_of_le : ∀ {b : NPComplete.BoundedWhile.Program} {ws : List ℕ} {B : ℕ},
  b.directWrites = some ws →
    (∀ w ∈ ws, w ≤ B) →
      ∀ {r : ℕ}, B < r → ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.loopEval b k σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_frame_of_le

/--
info: @NPComplete.BoundedWhile.loopEval_frame_of_writes : ∀ {b : NPComplete.BoundedWhile.Program} {ws : List ℕ} {r : ℕ},
  b.directWrites = some ws →
    r ∉ ws → ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.loopEval b k σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_frame_of_writes

/--
info: NPComplete.BoundedWhile.loopEval_index_inv : ∀ (b : NPComplete.BoundedWhile.Program) (N : ℕ)
  (I : ℕ → NPComplete.BoundedWhile.Store → Prop),
  (∀ (m : ℕ) (τ : NPComplete.BoundedWhile.Store), m < N → I m τ → I (m + 1) (b.eval τ)) →
    ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), k ≤ N → I 0 σ → I k (NPComplete.BoundedWhile.loopEval b k σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_index_inv

/--
info: NPComplete.BoundedWhile.loopEval_inv : ∀ (b : NPComplete.BoundedWhile.Program)
  (P : NPComplete.BoundedWhile.Store → Prop),
  (∀ (σ : NPComplete.BoundedWhile.Store), P σ → P (b.eval σ)) →
    ∀ (k : ℕ) (σ : NPComplete.BoundedWhile.Store), P σ → P (NPComplete.BoundedWhile.loopEval b k σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_inv

/--
info: NPComplete.BoundedWhile.loopEval_succ : ∀ (body : NPComplete.BoundedWhile.Program) (k : ℕ)
  (σ : NPComplete.BoundedWhile.Store),
  NPComplete.BoundedWhile.loopEval body (k + 1) σ = NPComplete.BoundedWhile.loopEval body k (body.eval σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_succ

/--
info: NPComplete.BoundedWhile.loopEval_succ_snoc : ∀ (body : NPComplete.BoundedWhile.Program) (k : ℕ)
  (σ : NPComplete.BoundedWhile.Store),
  NPComplete.BoundedWhile.loopEval body (k + 1) σ = body.eval (NPComplete.BoundedWhile.loopEval body k σ)
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_succ_snoc

/--
info: NPComplete.BoundedWhile.loopEval_zero : ∀ (body : NPComplete.BoundedWhile.Program) (σ : NPComplete.BoundedWhile.Store),
  NPComplete.BoundedWhile.loopEval body 0 σ = σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.loopEval_zero

/--
info: NPComplete.BoundedWhile.scanListCost : NPComplete.BoundedWhile.Program → List ℕ → ℕ → NPComplete.BoundedWhile.Store → ℕ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.scanListCost

/--
info: NPComplete.BoundedWhile.scanListCost_cons : ∀ (body : NPComplete.BoundedWhile.Program) (x : ℕ) (xs : List ℕ) (r : ℕ)
  (σ : NPComplete.BoundedWhile.Store),
  NPComplete.BoundedWhile.scanListCost body (x :: xs) r σ =
    body.cost (NPComplete.BoundedWhile.writeReg σ r x) +
      NPComplete.BoundedWhile.scanListCost body xs r (body.eval (NPComplete.BoundedWhile.writeReg σ r x))
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.scanListCost_cons

/--
info: NPComplete.BoundedWhile.scanListCost_le_of_body_le : ∀ (body : NPComplete.BoundedWhile.Program) (B : ℕ),
  (∀ (σ : NPComplete.BoundedWhile.Store), body.cost σ ≤ B) →
    ∀ (xs : List ℕ) (r : ℕ) (σ : NPComplete.BoundedWhile.Store),
      NPComplete.BoundedWhile.scanListCost body xs r σ ≤ xs.length * B
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.scanListCost_le_of_body_le

/--
info: NPComplete.BoundedWhile.scanListCost_le_of_body_le_inv : ∀ (body : NPComplete.BoundedWhile.Program) (r : ℕ)
  (P : NPComplete.BoundedWhile.Store → Prop) (B : ℕ),
  (∀ (σ : NPComplete.BoundedWhile.Store) (x : ℕ), P σ → P (body.eval (NPComplete.BoundedWhile.writeReg σ r x))) →
    (∀ (σ : NPComplete.BoundedWhile.Store) (x : ℕ), P σ → body.cost (NPComplete.BoundedWhile.writeReg σ r x) ≤ B) →
      ∀ (xs : List ℕ) (σ : NPComplete.BoundedWhile.Store),
        P σ → NPComplete.BoundedWhile.scanListCost body xs r σ ≤ xs.length * B
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.scanListCost_le_of_body_le_inv

/--
info: NPComplete.BoundedWhile.scanListCost_nil : ∀ (body : NPComplete.BoundedWhile.Program) (r : ℕ)
  (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.scanListCost body [] r σ = 0
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.scanListCost_nil

/--
info: NPComplete.BoundedWhile.scanListEval : NPComplete.BoundedWhile.Program →
  List ℕ → ℕ → NPComplete.BoundedWhile.Store → NPComplete.BoundedWhile.Store
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.scanListEval

/--
info: NPComplete.BoundedWhile.scanListEval_cons : ∀ (body : NPComplete.BoundedWhile.Program) (x : ℕ) (xs : List ℕ) (r : ℕ)
  (σ : NPComplete.BoundedWhile.Store),
  NPComplete.BoundedWhile.scanListEval body (x :: xs) r σ =
    NPComplete.BoundedWhile.scanListEval body xs r (body.eval (NPComplete.BoundedWhile.writeReg σ r x))
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.scanListEval_cons

/--
info: NPComplete.BoundedWhile.scanListEval_frame : ∀ (b : NPComplete.BoundedWhile.Program) (x r : ℕ),
  r ≠ x →
    (∀ (σ : NPComplete.BoundedWhile.Store), b.eval σ r = σ r) →
      ∀ (xs : List ℕ) (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.scanListEval b xs x σ r = σ r
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.scanListEval_frame

/--
info: NPComplete.BoundedWhile.scanListEval_nil : ∀ (body : NPComplete.BoundedWhile.Program) (r : ℕ)
  (σ : NPComplete.BoundedWhile.Store), NPComplete.BoundedWhile.scanListEval body [] r σ = σ
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.scanListEval_nil

/--
info: NPComplete.BoundedWhile.writeReg : NPComplete.BoundedWhile.Store → ℕ → ℕ → NPComplete.BoundedWhile.Store
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.writeReg

/--
info: @[expose] def NPComplete.BoundedWhile.writeReg : NPComplete.BoundedWhile.Store →
  ℕ → ℕ → NPComplete.BoundedWhile.Store :=
fun σ r v r' => if r' = r then v else σ r'
-/
#guard_msgs in
#print NPComplete.BoundedWhile.writeReg

/--
info: NPComplete.BoundedWhile.writeReg_diff : ∀ (σ : NPComplete.BoundedWhile.Store) (r v r' : ℕ),
  r' ≠ r → NPComplete.BoundedWhile.writeReg σ r v r' = σ r'
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.writeReg_diff

/--
info: NPComplete.BoundedWhile.writeReg_same : ∀ (σ : NPComplete.BoundedWhile.Store) (r v : ℕ),
  NPComplete.BoundedWhile.writeReg σ r v r = v
-/
#guard_msgs in
#check @NPComplete.BoundedWhile.writeReg_same

/--
info: NPComplete.CookLevin.CNF : Type
-/
#guard_msgs in
#check @NPComplete.CookLevin.CNF

/--
info: structure NPComplete.CookLevin.CNF : Type
number of parameters: 0
fields:
  NPComplete.CookLevin.CNF.clauses : List NPComplete.CookLevin.Clause
constructor:
  NPComplete.CookLevin.CNF.mk (clauses : List NPComplete.CookLevin.Clause) : NPComplete.CookLevin.CNF
-/
#guard_msgs in
#print NPComplete.CookLevin.CNF

/--
info: NPComplete.CookLevin.CNF.append : NPComplete.CookLevin.CNF → NPComplete.CookLevin.CNF → NPComplete.CookLevin.CNF
-/
#guard_msgs in
#check @NPComplete.CookLevin.CNF.append

/--
info: @[expose] def NPComplete.CookLevin.CNF.append : NPComplete.CookLevin.CNF →
  NPComplete.CookLevin.CNF → NPComplete.CookLevin.CNF :=
fun φ ψ => { clauses := φ.clauses ++ ψ.clauses }
-/
#guard_msgs in
#print NPComplete.CookLevin.CNF.append

/--
info: NPComplete.CookLevin.Clause : Type
-/
#guard_msgs in
#check @NPComplete.CookLevin.Clause

/--
info: structure NPComplete.CookLevin.Clause : Type
number of parameters: 0
fields:
  NPComplete.CookLevin.Clause.lits : List NPComplete.SAT.Literal
constructor:
  NPComplete.CookLevin.Clause.mk (lits : List NPComplete.SAT.Literal) : NPComplete.CookLevin.Clause
-/
#guard_msgs in
#print NPComplete.CookLevin.Clause

/--
info: NPComplete.CookLevin.Clause.Satisfied : NPComplete.SAT.Literal.Assignment → NPComplete.CookLevin.Clause → Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.Clause.Satisfied

/--
info: @[expose] def NPComplete.CookLevin.Clause.Satisfied : NPComplete.SAT.Literal.Assignment →
  NPComplete.CookLevin.Clause → Prop :=
fun τ c => ∃ l ∈ c.lits, NPComplete.SAT.Literal.eval τ l = true
-/
#guard_msgs in
#print NPComplete.CookLevin.Clause.Satisfied

/--
info: @NPComplete.CookLevin.InNP : {α : Type} → (α → List Bool) → (α → Prop) → Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.InNP

/--
info: @[expose] def NPComplete.CookLevin.InNP : {α : Type} → (α → List Bool) → (α → Prop) → Prop :=
fun {α} enc L =>
  ∃ p V,
    (∀ (x : α), L x ↔ ∃ w, w.length ≤ Polynomial.eval (enc x).length p ∧ V x w = true) ∧
      Nonempty
        (NPComplete.CookLevin.TM0ComputableInPolyTime (fun xw => NPComplete.CookLevin.pairBits (enc xw.1) xw.2)
          Computability.encodeBool fun xw => V xw.1 xw.2)
-/
#guard_msgs in
#print NPComplete.CookLevin.InNP

/--
info: @NPComplete.CookLevin.InP : {α : Type} → (α → List Bool) → (α → Prop) → Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.InP

/--
info: @[expose] def NPComplete.CookLevin.InP : {α : Type} → (α → List Bool) → (α → Prop) → Prop :=
fun {α} enc L =>
  ∃ f,
    Nonempty (NPComplete.CookLevin.TM0ComputableInPolyTime enc Computability.encodeBool f) ∧ ∀ (x : α), f x = true ↔ L x
-/
#guard_msgs in
#print NPComplete.CookLevin.InP

/--
info: @NPComplete.CookLevin.InP.of_reduction : ∀ {α β : Type} {eα : α → List Bool} {eβ : β → List Bool} {Lα : α → Prop}
  {Lβ : β → Prop} (r : NPComplete.CookLevin.PolyTimeReduction eα eβ Lα Lβ),
  NPComplete.CookLevin.InP eβ Lβ → NPComplete.CookLevin.InP eα Lα
-/
#guard_msgs in
#check @NPComplete.CookLevin.InP.of_reduction

/--
info: @NPComplete.CookLevin.InP.respects_enc : ∀ {α : Type} {enc : α → List Bool} {L : α → Prop},
  NPComplete.CookLevin.InP enc L → ∀ {x y : α}, enc x = enc y → (L x ↔ L y)
-/
#guard_msgs in
#check @NPComplete.CookLevin.InP.respects_enc

/--
info: @NPComplete.CookLevin.InNP.respects_enc : ∀ {α : Type} {enc : α → List Bool} {L : α → Prop},
  NPComplete.CookLevin.InNP enc L → ∀ {x y : α}, enc x = enc y → (L x ↔ L y)
-/
#guard_msgs in
#check @NPComplete.CookLevin.InNP.respects_enc

/--
info: @NPComplete.CookLevin.NPComplete : {β : Type} → (β → List Bool) → (β → Prop) → Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.NPComplete

/--
info: @[expose] def NPComplete.CookLevin.NPComplete : {β : Type} → (β → List Bool) → (β → Prop) → Prop :=
fun {β} eb L => NPComplete.CookLevin.InNP eb L ∧ NPComplete.CookLevin.NPHard eb L
-/
#guard_msgs in
#print NPComplete.CookLevin.NPComplete

/--
info: @NPComplete.CookLevin.NPComplete.of_threeSAT : ∀ {β : Type} {eb : β → List Bool} {L : β → Prop},
  NPComplete.CookLevin.InNP eb L →
    ∀
      (r :
        NPComplete.CookLevin.PolyTimeReduction NPComplete.SAT.ValidThreeCNF.encode eb
          (NPComplete.SAT.ThreeSAT ∘ Subtype.val) L),
      NPComplete.CookLevin.NPComplete eb L
-/
#guard_msgs in
#check @NPComplete.CookLevin.NPComplete.of_threeSAT

/--
info: @NPComplete.CookLevin.NPHard : {β : Type} → (β → List Bool) → (β → Prop) → Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.NPHard

/--
info: @[expose] def NPComplete.CookLevin.NPHard : {β : Type} → (β → List Bool) → (β → Prop) → Prop :=
fun {β} eb L =>
  ∀ {α : Type} (ea : α → List Bool) (La : α → Prop),
    NPComplete.CookLevin.InNP ea La → Nonempty (NPComplete.CookLevin.PolyTimeReduction ea eb La L)
-/
#guard_msgs in
#print NPComplete.CookLevin.NPHard

/--
info: @NPComplete.CookLevin.NPHard.of_reduction : ∀ {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {La : α → Prop}
  {Lb : β → Prop},
  NPComplete.CookLevin.NPHard ea La →
    ∀ (r : NPComplete.CookLevin.PolyTimeReduction ea eb La Lb), NPComplete.CookLevin.NPHard eb Lb
-/
#guard_msgs in
#check @NPComplete.CookLevin.NPHard.of_reduction

/--
info: @NPComplete.CookLevin.NPHard.of_threeSAT : ∀ {β : Type} {eb : β → List Bool} {L : β → Prop}
  (r :
    NPComplete.CookLevin.PolyTimeReduction NPComplete.SAT.ValidThreeCNF.encode eb
      (NPComplete.SAT.ThreeSAT ∘ Subtype.val) L),
  NPComplete.CookLevin.NPHard eb L
-/
#guard_msgs in
#check @NPComplete.CookLevin.NPHard.of_threeSAT

/--
info: NPComplete.CookLevin.PeqNP : Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.PeqNP

/--
info: @[expose] def NPComplete.CookLevin.PeqNP : Prop :=
∀ {α : Type} (enc : α → List Bool) (L : α → Prop), NPComplete.CookLevin.InNP enc L → NPComplete.CookLevin.InP enc L
-/
#guard_msgs in
#print NPComplete.CookLevin.PeqNP

/--
info: NPComplete.CookLevin.PneNP : Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.PneNP

/--
info: @[expose] def NPComplete.CookLevin.PneNP : Prop :=
¬NPComplete.CookLevin.PeqNP
-/
#guard_msgs in
#print NPComplete.CookLevin.PneNP

/--
info: @NPComplete.CookLevin.PolyTimeReduction : {α β : Type} →
  (α → List Bool) → (β → List Bool) → (α → Prop) → (β → Prop) → Type
-/
#guard_msgs in
#check @NPComplete.CookLevin.PolyTimeReduction

/--
info: structure NPComplete.CookLevin.PolyTimeReduction {α β : Type} (eα : α → List Bool) (eβ : β → List Bool) (Lα : α → Prop)
  (Lβ : β → Prop) : Type
number of parameters: 6
fields:
  NPComplete.CookLevin.PolyTimeReduction.map : α → β
  NPComplete.CookLevin.PolyTimeReduction.computable : Nonempty
      (NPComplete.CookLevin.TM0ComputableInPolyTime eα eβ self.map)
  NPComplete.CookLevin.PolyTimeReduction.correct : ∀ (x : α), Lα x ↔ Lβ (self.map x)
constructor:
  NPComplete.CookLevin.PolyTimeReduction.mk {α β : Type} {eα : α → List Bool} {eβ : β → List Bool} {Lα : α → Prop}
    {Lβ : β → Prop} (map : α → β) (computable : Nonempty (NPComplete.CookLevin.TM0ComputableInPolyTime eα eβ map))
    (correct : ∀ (x : α), Lα x ↔ Lβ (map x)) : NPComplete.CookLevin.PolyTimeReduction eα eβ Lα Lβ
-/
#guard_msgs in
#print NPComplete.CookLevin.PolyTimeReduction

/--
info: @NPComplete.CookLevin.PolyTimeReduction.trans : {α β γ : Type} →
  {eα : α → List Bool} →
    {eβ : β → List Bool} →
      {eγ : γ → List Bool} →
        {Lα : α → Prop} →
          {Lβ : β → Prop} →
            {Lγ : γ → Prop} →
              NPComplete.CookLevin.PolyTimeReduction eα eβ Lα Lβ →
                NPComplete.CookLevin.PolyTimeReduction eβ eγ Lβ Lγ → NPComplete.CookLevin.PolyTimeReduction eα eγ Lα Lγ
-/
#guard_msgs in
#check @NPComplete.CookLevin.PolyTimeReduction.trans

/--
info: @NPComplete.CookLevin.PromisePolyDecidable : {α : Type} →
  (α → NPComplete.BitEncoding.Bits) → (α → Prop) → (α → Prop) → Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.PromisePolyDecidable

/--
info: @[expose] def NPComplete.CookLevin.PromisePolyDecidable : {α : Type} →
  (α → NPComplete.BitEncoding.Bits) → (α → Prop) → (α → Prop) → Prop :=
fun {α} enc D L =>
  ∃ f,
    Nonempty (Turing.TM2ComputableInPolyTime (enc ∘ Subtype.val) NPComplete.BitEncoding.encodeBool f) ∧
      ∀ (x : { x // D x }), f x = true ↔ L ↑x
-/
#guard_msgs in
#print NPComplete.CookLevin.PromisePolyDecidable

/--
info: NPComplete.CookLevin.SAT : NPComplete.CookLevin.CNF → Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.SAT

/--
info: @[expose] def NPComplete.CookLevin.SAT : NPComplete.CookLevin.CNF → Prop :=
fun φ => ∃ τ, ∀ c ∈ φ.clauses, NPComplete.CookLevin.Clause.Satisfied τ c
-/
#guard_msgs in
#print NPComplete.CookLevin.SAT

/--
info: NPComplete.CookLevin.TM0ComputableAux : (Γ : Type) → [Fintype Γ] → Type 1
-/
#guard_msgs in
#check @NPComplete.CookLevin.TM0ComputableAux

/--
info: structure NPComplete.CookLevin.TM0ComputableAux (Γ : Type) [Fintype Γ] : Type 1
number of parameters: 2
fields:
  NPComplete.CookLevin.TM0ComputableAux.Λ : Type
  NPComplete.CookLevin.TM0ComputableAux.ΛInhabited : Inhabited self.Λ
  NPComplete.CookLevin.TM0ComputableAux.ΛDecidableEq : DecidableEq self.Λ
  NPComplete.CookLevin.TM0ComputableAux.M : Turing.TM0.Machine (Option Γ) self.Λ
  NPComplete.CookLevin.TM0ComputableAux.S : Finset self.Λ
  NPComplete.CookLevin.TM0ComputableAux.supports : Turing.TM0.Supports self.M ↑self.S
constructor:
  NPComplete.CookLevin.TM0ComputableAux.mk {Γ : Type} [Fintype Γ] (Λ : Type) [ΛInhabited : Inhabited Λ]
    [ΛDecidableEq : DecidableEq Λ] (M : Turing.TM0.Machine (Option Γ) Λ) (S : Finset Λ)
    (supports : Turing.TM0.Supports M ↑S) : NPComplete.CookLevin.TM0ComputableAux Γ
-/
#guard_msgs in
#print NPComplete.CookLevin.TM0ComputableAux

/--
info: @NPComplete.CookLevin.TM0ComputableInPolyTime : {α β Γ : Type} →
  [Fintype Γ] → (α → List Γ) → (β → List Γ) → (α → β) → Type 1
-/
#guard_msgs in
#check @NPComplete.CookLevin.TM0ComputableInPolyTime

/--
info: structure NPComplete.CookLevin.TM0ComputableInPolyTime {α β Γ : Type} [Fintype Γ] (ea : α → List Γ) (eb : β → List Γ)
  (f : α → β) : Type 1
number of parameters: 7
parents:
  NPComplete.CookLevin.TM0ComputableInPolyTime.toTM0ComputableAux : NPComplete.CookLevin.TM0ComputableAux Γ
fields:
  NPComplete.CookLevin.TM0ComputableAux.Λ : Type
  NPComplete.CookLevin.TM0ComputableAux.ΛInhabited : Inhabited self.Λ
  NPComplete.CookLevin.TM0ComputableAux.ΛDecidableEq : DecidableEq self.Λ
  NPComplete.CookLevin.TM0ComputableAux.M : Turing.TM0.Machine (Option Γ) self.Λ
  NPComplete.CookLevin.TM0ComputableAux.S : Finset self.Λ
  NPComplete.CookLevin.TM0ComputableAux.supports : Turing.TM0.Supports self.M ↑self.S
  NPComplete.CookLevin.TM0ComputableInPolyTime.time : Polynomial ℕ
  NPComplete.CookLevin.TM0ComputableInPolyTime.outputsFun : ∀ (a : α),
      NPComplete.CookLevin.MachineOutputsInTime self.M (NPComplete.CookLevin.tapeSymbols (ea a))
        (NPComplete.CookLevin.tapeSymbols (eb (f a))) (Polynomial.eval (ea a).length self.time)
constructor:
  NPComplete.CookLevin.TM0ComputableInPolyTime.mk {α β Γ : Type} [Fintype Γ] {ea : α → List Γ} {eb : β → List Γ}
    {f : α → β} (toTM0ComputableAux : NPComplete.CookLevin.TM0ComputableAux Γ) (time : Polynomial ℕ)
    (outputsFun :
      ∀ (a : α),
        NPComplete.CookLevin.MachineOutputsInTime toTM0ComputableAux.M (NPComplete.CookLevin.tapeSymbols (ea a))
          (NPComplete.CookLevin.tapeSymbols (eb (f a))) (Polynomial.eval (ea a).length time)) :
    NPComplete.CookLevin.TM0ComputableInPolyTime ea eb f
field notation resolution order:
  NPComplete.CookLevin.TM0ComputableInPolyTime, NPComplete.CookLevin.TM0ComputableAux
-/
#guard_msgs in
#print NPComplete.CookLevin.TM0ComputableInPolyTime

/--
info: @NPComplete.CookLevin.TM2to1.StepsTo : {α : Type u_1} → (α → Option α) → α → α → ℕ → Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.TM2to1.StepsTo

/--
info: @[expose] def NPComplete.CookLevin.TM2to1.StepsTo.{u_5} : {α : Type u_5} → (α → Option α) → α → α → ℕ → Prop :=
fun {α} f a b t => (fun s => s.bind f)^[t] (some a) = some b
-/
#guard_msgs in
#print NPComplete.CookLevin.TM2to1.StepsTo

/--
info: NPComplete.CookLevin.encodeCNF : NPComplete.CookLevin.CNF → NPComplete.BitEncoding.Bits
-/
#guard_msgs in
#check @NPComplete.CookLevin.encodeCNF

/--
info: @[expose] def NPComplete.CookLevin.encodeCNF : NPComplete.CookLevin.CNF → NPComplete.BitEncoding.Bits :=
fun φ => NPComplete.BitEncoding.encodeList NPComplete.CookLevin.encodeClause φ.clauses
-/
#guard_msgs in
#print NPComplete.CookLevin.encodeCNF

/--
info: NPComplete.CookLevin.encodeClause : NPComplete.CookLevin.Clause → NPComplete.BitEncoding.Bits
-/
#guard_msgs in
#check @NPComplete.CookLevin.encodeClause

/--
info: @[expose] def NPComplete.CookLevin.encodeClause : NPComplete.CookLevin.Clause → NPComplete.BitEncoding.Bits :=
fun c => NPComplete.BitEncoding.encodeList NPComplete.SAT.encodeLiteral c.lits
-/
#guard_msgs in
#print NPComplete.CookLevin.encodeClause

/--
info: @NPComplete.CookLevin.MachineOutputsInTime : {Γ : Type u_1} →
  {Λ : Type u_2} → [Inhabited Γ] → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → List Γ → ℕ → Prop
-/
#guard_msgs in
#check @NPComplete.CookLevin.MachineOutputsInTime

/--
info: @[expose] def NPComplete.CookLevin.MachineOutputsInTime.{u_1, u_2} : {Γ : Type u_1} →
  {Λ : Type u_2} → [Inhabited Γ] → [inst : Inhabited Λ] → Turing.TM0.Machine Γ Λ → List Γ → List Γ → ℕ → Prop :=
fun {Γ} {Λ} [Inhabited Γ] [Inhabited Λ] M input output m =>
  ∃ q,
    ∃ t ≤ m,
      NPComplete.CookLevin.TM2to1.StepsTo (Turing.TM0.step M) (Turing.TM0.init input)
          { q := q, Tape := Turing.Tape.mk₁ output } t ∧
        Turing.TM0.step M { q := q, Tape := Turing.Tape.mk₁ output } = none
-/
#guard_msgs in
#print NPComplete.CookLevin.MachineOutputsInTime

/--
info: NPComplete.CookLevin.p_ne_np_implies_h3sat : NPComplete.CookLevin.PneNP →
  ¬NPComplete.CookLevin.PromisePolyDecidable NPComplete.SAT.ValidThreeCNF.encode (fun x => True)
      (NPComplete.SAT.ThreeSAT ∘ Subtype.val)
-/
#guard_msgs in
#check @NPComplete.CookLevin.p_ne_np_implies_h3sat

/--
info: NPComplete.CookLevin.pairBits : List Bool → List Bool → List Bool
-/
#guard_msgs in
#check @NPComplete.CookLevin.pairBits

/--
info: @[expose] def NPComplete.CookLevin.pairBits : List Bool → List Bool → List Bool :=
fun x w => List.flatMap (fun b => [true, b]) x ++ [false] ++ w
-/
#guard_msgs in
#print NPComplete.CookLevin.pairBits

/--
info: NPComplete.CookLevin.pairBits_length : ∀ (x w : List Bool),
  (NPComplete.CookLevin.pairBits x w).length = 2 * x.length + 1 + w.length
-/
#guard_msgs in
#check @NPComplete.CookLevin.pairBits_length

/--
info: @NPComplete.CookLevin.promisePolyDecidable_of_false : ∀ {α : Type} (enc : α → NPComplete.BitEncoding.Bits)
  (L : α → Prop), NPComplete.CookLevin.PromisePolyDecidable enc (fun x => False) L
-/
#guard_msgs in
#check @NPComplete.CookLevin.promisePolyDecidable_of_false

/--
info: @NPComplete.CookLevin.promisePolyDecidable_to_InP : ∀ {α : Type} {enc : α → List Bool} {L : α → Prop},
  NPComplete.CookLevin.PromisePolyDecidable enc (fun x => True) L → NPComplete.CookLevin.InP enc L
-/
#guard_msgs in
#check @NPComplete.CookLevin.promisePolyDecidable_to_InP

/--
info: NPComplete.CookLevin.sat_InP_implies_PeqNP : NPComplete.CookLevin.InP NPComplete.CookLevin.encodeCNF
    NPComplete.CookLevin.SAT →
  NPComplete.CookLevin.PeqNP
-/
#guard_msgs in
#check @NPComplete.CookLevin.sat_InP_implies_PeqNP

/--
info: NPComplete.CookLevin.sat_NPComplete : NPComplete.CookLevin.NPComplete NPComplete.CookLevin.encodeCNF
  NPComplete.CookLevin.SAT
-/
#guard_msgs in
#check @NPComplete.CookLevin.sat_NPComplete

/--
info: @NPComplete.CookLevin.sat_NPHard : NPComplete.CookLevin.NPHard NPComplete.CookLevin.encodeCNF NPComplete.CookLevin.SAT
-/
#guard_msgs in
#check @NPComplete.CookLevin.sat_NPHard

/--
info: @NPComplete.CookLevin.sat_append_of : ∀ {φ ψ : NPComplete.CookLevin.CNF} {τ : NPComplete.SAT.Literal.Assignment},
  (∀ c ∈ φ.clauses, NPComplete.CookLevin.Clause.Satisfied τ c) →
    (∀ c ∈ ψ.clauses, NPComplete.CookLevin.Clause.Satisfied τ c) → NPComplete.CookLevin.SAT (φ.append ψ)
-/
#guard_msgs in
#check @NPComplete.CookLevin.sat_append_of

/--
info: NPComplete.CookLevin.sat_inNP : NPComplete.CookLevin.InNP NPComplete.CookLevin.encodeCNF NPComplete.CookLevin.SAT
-/
#guard_msgs in
#check @NPComplete.CookLevin.sat_inNP

/--
info: NPComplete.CookLevin.sat_nil : NPComplete.CookLevin.SAT { clauses := [] }
-/
#guard_msgs in
#check @NPComplete.CookLevin.sat_nil

/--
info: @NPComplete.CookLevin.sat_of_append_left : ∀ {φ ψ : NPComplete.CookLevin.CNF},
  NPComplete.CookLevin.SAT (φ.append ψ) → NPComplete.CookLevin.SAT φ
-/
#guard_msgs in
#check @NPComplete.CookLevin.sat_of_append_left

/--
info: @NPComplete.CookLevin.sat_of_append_right : ∀ {φ ψ : NPComplete.CookLevin.CNF},
  NPComplete.CookLevin.SAT (φ.append ψ) → NPComplete.CookLevin.SAT ψ
-/
#guard_msgs in
#check @NPComplete.CookLevin.sat_of_append_right

/--
info: @NPComplete.CookLevin.stepsTo_of_reaches : ∀ {α : Type} {f : α → Option α} {a b : α},
  StateTransition.Reaches f a b → ∃ t, NPComplete.CookLevin.TM2to1.StepsTo f a b t
-/
#guard_msgs in
#check @NPComplete.CookLevin.stepsTo_of_reaches

/--
info: @NPComplete.CookLevin.tapeSymbols : {Γ : Type u_1} → List Γ → List (Option Γ)
-/
#guard_msgs in
#check @NPComplete.CookLevin.tapeSymbols

/--
info: NPComplete.CookLevin.threeSAT_InP_implies_PeqNP : NPComplete.CookLevin.InP NPComplete.SAT.ValidThreeCNF.encode
    (NPComplete.SAT.ThreeSAT ∘ Subtype.val) →
  NPComplete.CookLevin.PeqNP
-/
#guard_msgs in
#check @NPComplete.CookLevin.threeSAT_InP_implies_PeqNP

/--
info: NPComplete.CookLevin.threeSAT_NPComplete : NPComplete.CookLevin.NPComplete NPComplete.SAT.ValidThreeCNF.encode
  (NPComplete.SAT.ThreeSAT ∘ Subtype.val)
-/
#guard_msgs in
#check @NPComplete.CookLevin.threeSAT_NPComplete

/--
info: @NPComplete.CookLevin.threeSAT_NPHard : NPComplete.CookLevin.NPHard NPComplete.SAT.ValidThreeCNF.encode
  (NPComplete.SAT.ThreeSAT ∘ Subtype.val)
-/
#guard_msgs in
#check @NPComplete.CookLevin.threeSAT_NPHard

/--
info: NPComplete.CookLevin.threeSAT_inNP : NPComplete.CookLevin.InNP NPComplete.SAT.ValidThreeCNF.encode
  (NPComplete.SAT.ThreeSAT ∘ Subtype.val)
-/
#guard_msgs in
#check @NPComplete.CookLevin.threeSAT_inNP

/--
info: NPComplete.SAT.Literal : Type
-/
#guard_msgs in
#check @NPComplete.SAT.Literal

/--
info: inductive NPComplete.SAT.Literal : Type
number of parameters: 0
constructors:
NPComplete.SAT.Literal.pos : ℕ → NPComplete.SAT.Literal
NPComplete.SAT.Literal.neg : ℕ → NPComplete.SAT.Literal
-/
#guard_msgs in
#print NPComplete.SAT.Literal

/--
info: NPComplete.SAT.Literal.Assignment : Type
-/
#guard_msgs in
#check @NPComplete.SAT.Literal.Assignment

/--
info: @[expose] def NPComplete.SAT.Literal.Assignment : Type :=
ℕ → Bool
-/
#guard_msgs in
#print NPComplete.SAT.Literal.Assignment

/--
info: NPComplete.SAT.Literal.eval : NPComplete.SAT.Literal.Assignment → NPComplete.SAT.Literal → Bool
-/
#guard_msgs in
#check @NPComplete.SAT.Literal.eval

/--
info: NPComplete.SAT.Literal.is_pos : NPComplete.SAT.Literal → Bool
-/
#guard_msgs in
#check @NPComplete.SAT.Literal.is_pos

/--
info: @[expose] def NPComplete.SAT.Literal.is_pos : NPComplete.SAT.Literal → Bool :=
fun x =>
  match x with
  | NPComplete.SAT.Literal.pos a => true
  | NPComplete.SAT.Literal.neg a => false
-/
#guard_msgs in
#print NPComplete.SAT.Literal.is_pos

/--
info: NPComplete.SAT.Literal.is_pos_negate : ∀ (l : NPComplete.SAT.Literal), l.negate.is_pos = !l.is_pos
-/
#guard_msgs in
#check @NPComplete.SAT.Literal.is_pos_negate

/--
info: NPComplete.SAT.Literal.negate : NPComplete.SAT.Literal → NPComplete.SAT.Literal
-/
#guard_msgs in
#check @NPComplete.SAT.Literal.negate

/--
info: @[expose] def NPComplete.SAT.Literal.negate : NPComplete.SAT.Literal → NPComplete.SAT.Literal :=
fun x =>
  match x with
  | NPComplete.SAT.Literal.pos i => NPComplete.SAT.Literal.neg i
  | NPComplete.SAT.Literal.neg i => NPComplete.SAT.Literal.pos i
-/
#guard_msgs in
#print NPComplete.SAT.Literal.negate

/--
info: NPComplete.SAT.Literal.var : NPComplete.SAT.Literal → ℕ
-/
#guard_msgs in
#check @NPComplete.SAT.Literal.var

/--
info: NPComplete.SAT.Literal.var_negate : ∀ (l : NPComplete.SAT.Literal), l.negate.var = l.var
-/
#guard_msgs in
#check @NPComplete.SAT.Literal.var_negate

/--
info: NPComplete.SAT.ThreeCNF : Type
-/
#guard_msgs in
#check @NPComplete.SAT.ThreeCNF

/--
info: structure NPComplete.SAT.ThreeCNF : Type
number of parameters: 0
fields:
  NPComplete.SAT.ThreeCNF.numVars : ℕ
  NPComplete.SAT.ThreeCNF.clauses : List NPComplete.SAT.ThreeClause
constructor:
  NPComplete.SAT.ThreeCNF.mk (numVars : ℕ) (clauses : List NPComplete.SAT.ThreeClause) : NPComplete.SAT.ThreeCNF
-/
#guard_msgs in
#print NPComplete.SAT.ThreeCNF

/--
info: NPComplete.SAT.ThreeCNF.Bounded : NPComplete.SAT.ThreeCNF → Prop
-/
#guard_msgs in
#check @NPComplete.SAT.ThreeCNF.Bounded

/--
info: @[expose] def NPComplete.SAT.ThreeCNF.Bounded : NPComplete.SAT.ThreeCNF → Prop :=
fun f => ∀ c ∈ f.clauses, ∀ l ∈ c.literals, l.var < f.numVars
-/
#guard_msgs in
#print NPComplete.SAT.ThreeCNF.Bounded

/--
info: NPComplete.SAT.ThreeCNF.Satisfied : NPComplete.SAT.Literal.Assignment → NPComplete.SAT.ThreeCNF → Prop
-/
#guard_msgs in
#check @NPComplete.SAT.ThreeCNF.Satisfied

/--
info: @[expose] def NPComplete.SAT.ThreeCNF.Satisfied : NPComplete.SAT.Literal.Assignment → NPComplete.SAT.ThreeCNF → Prop :=
fun a f => ∀ c ∈ f.clauses, NPComplete.SAT.ThreeClause.Satisfied a c
-/
#guard_msgs in
#print NPComplete.SAT.ThreeCNF.Satisfied

/--
info: NPComplete.SAT.ThreeClause : Type
-/
#guard_msgs in
#check @NPComplete.SAT.ThreeClause

/--
info: structure NPComplete.SAT.ThreeClause : Type
number of parameters: 0
fields:
  NPComplete.SAT.ThreeClause.l1 : NPComplete.SAT.Literal
  NPComplete.SAT.ThreeClause.l2 : NPComplete.SAT.Literal
  NPComplete.SAT.ThreeClause.l3 : NPComplete.SAT.Literal
constructor:
  NPComplete.SAT.ThreeClause.mk (l1 l2 l3 : NPComplete.SAT.Literal) : NPComplete.SAT.ThreeClause
-/
#guard_msgs in
#print NPComplete.SAT.ThreeClause

/--
info: NPComplete.SAT.ThreeClause.literals : NPComplete.SAT.ThreeClause → List NPComplete.SAT.Literal
-/
#guard_msgs in
#check @NPComplete.SAT.ThreeClause.literals

/--
info: NPComplete.SAT.ThreeClause.Satisfied : NPComplete.SAT.Literal.Assignment → NPComplete.SAT.ThreeClause → Prop
-/
#guard_msgs in
#check @NPComplete.SAT.ThreeClause.Satisfied

/--
info: @[expose] def NPComplete.SAT.ThreeClause.Satisfied : NPComplete.SAT.Literal.Assignment →
  NPComplete.SAT.ThreeClause → Prop :=
fun a c =>
  NPComplete.SAT.Literal.eval a c.l1 = true ∨
    NPComplete.SAT.Literal.eval a c.l2 = true ∨ NPComplete.SAT.Literal.eval a c.l3 = true
-/
#guard_msgs in
#print NPComplete.SAT.ThreeClause.Satisfied

/--
info: NPComplete.SAT.ThreeSAT : NPComplete.SAT.ThreeCNF → Prop
-/
#guard_msgs in
#check @NPComplete.SAT.ThreeSAT

/--
info: @[expose] def NPComplete.SAT.ThreeSAT : NPComplete.SAT.ThreeCNF → Prop :=
fun f => ∃ a, NPComplete.SAT.ThreeCNF.Satisfied a f
-/
#guard_msgs in
#print NPComplete.SAT.ThreeSAT

/--
info: NPComplete.SAT.ValidThreeCNF : Type
-/
#guard_msgs in
#check @NPComplete.SAT.ValidThreeCNF

/--
info: @[reducible, expose] def NPComplete.SAT.ValidThreeCNF : Type :=
{ f // f.Bounded }
-/
#guard_msgs in
#print NPComplete.SAT.ValidThreeCNF

/--
info: NPComplete.SAT.ValidThreeCNF.encode : NPComplete.SAT.ValidThreeCNF → NPComplete.BitEncoding.Bits
-/
#guard_msgs in
#check @NPComplete.SAT.ValidThreeCNF.encode

/--
info: @[expose] def NPComplete.SAT.ValidThreeCNF.encode : NPComplete.SAT.ValidThreeCNF → NPComplete.BitEncoding.Bits :=
fun f => NPComplete.SAT.encodeThreeCNF ↑f
-/
#guard_msgs in
#print NPComplete.SAT.ValidThreeCNF.encode

/--
info: NPComplete.SAT.ValidThreeCNF.encode_injective : Function.Injective NPComplete.SAT.ValidThreeCNF.encode
-/
#guard_msgs in
#check @NPComplete.SAT.ValidThreeCNF.encode_injective

/--
info: NPComplete.SAT.encodeLiteral : NPComplete.SAT.Literal → NPComplete.BitEncoding.Bits
-/
#guard_msgs in
#check @NPComplete.SAT.encodeLiteral

/--
info: @[expose] def NPComplete.SAT.encodeLiteral : NPComplete.SAT.Literal → NPComplete.BitEncoding.Bits :=
fun x =>
  match x with
  | NPComplete.SAT.Literal.pos i => false :: NPComplete.BitEncoding.encodeNat i
  | NPComplete.SAT.Literal.neg i => true :: NPComplete.BitEncoding.encodeNat i
-/
#guard_msgs in
#print NPComplete.SAT.encodeLiteral

/--
info: NPComplete.SAT.encodeThreeCNF : NPComplete.SAT.ThreeCNF → NPComplete.BitEncoding.Bits
-/
#guard_msgs in
#check @NPComplete.SAT.encodeThreeCNF

/--
info: @[expose] def NPComplete.SAT.encodeThreeCNF : NPComplete.SAT.ThreeCNF → NPComplete.BitEncoding.Bits :=
fun f =>
  NPComplete.BitEncoding.encodeNat f.numVars ++
    NPComplete.BitEncoding.encodeList NPComplete.SAT.encodeThreeClause f.clauses
-/
#guard_msgs in
#print NPComplete.SAT.encodeThreeCNF

/--
info: NPComplete.SAT.encodeThreeClause : NPComplete.SAT.ThreeClause → NPComplete.BitEncoding.Bits
-/
#guard_msgs in
#check @NPComplete.SAT.encodeThreeClause

/--
info: @[expose] def NPComplete.SAT.encodeThreeClause : NPComplete.SAT.ThreeClause → NPComplete.BitEncoding.Bits :=
fun c => NPComplete.SAT.encodeLiteral c.l1 ++ NPComplete.SAT.encodeLiteral c.l2 ++ NPComplete.SAT.encodeLiteral c.l3
-/
#guard_msgs in
#print NPComplete.SAT.encodeThreeClause

/--
info: NPComplete.arenaAddr : ℕ → ℕ → ℕ → ℕ → ℕ
-/
#guard_msgs in
#check @NPComplete.arenaAddr

/--
info: NPComplete.arenaAddr_eq : ∀ (arenaBase stride i lane : ℕ),
  NPComplete.arenaAddr arenaBase stride i lane = arenaBase + stride * i + lane
-/
#guard_msgs in
#check @NPComplete.arenaAddr_eq

/--
info: NPComplete.arenaAddr_ne : ∀ (arenaBase stride i₁ l₁ i₂ l₂ : ℕ),
  l₁ < stride →
    l₂ < stride →
      i₁ ≠ i₂ ∨ l₁ ≠ l₂ → NPComplete.arenaAddr arenaBase stride i₁ l₁ ≠ NPComplete.arenaAddr arenaBase stride i₂ l₂
-/
#guard_msgs in
#check @NPComplete.arenaAddr_ne
