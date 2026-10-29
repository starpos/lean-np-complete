module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.BoundedWhile.Basic

/-!
# Frame reasoning for the bounded-WHILE DSL

A program that never writes register `r` leaves `r` unchanged.  Proving this by hand
means unfolding the program and chaining `writeReg_diff` for every command, and the
same chain is rewritten for every program.  `Program.directWrites` computes a
syntactic write set once, and `Program.eval_frame` turns "`r` is outside the write
set" into the frame equation by a single induction on `Program`.  A program's
footprint can therefore be established once and shared by all of its frame lemmas.

Programs containing an indirect write (`assignInd`) are not analyzed by the syntactic
write set, because the destination depends on the store.  `AvoidsAbove` covers the
case where that destination has a static lower bound; a destination computed from
the store is not claimed here.

The generic loop lemmas (`loopEval_inv`, `loopEval_fixed`) live here as well so that
invariant-style arguments over `loopEval` do not have to be re-proved per program.
-/

@[expose] public section

namespace NPComplete.BoundedWhile

/-- Syntactic over-approximation of the registers a program writes directly.

`some ws` means every register the program may write is a member of `ws`.
`none` means the program is not analyzable (an `assignInd` occurs); it does NOT mean
that the program writes nothing. -/
@[stable_api] def Program.directWrites : Program → Option (List ℕ)
  | .skip => some []
  | .assign r _ => some [r]
  | .assignInd _ _ => none
  | .seq p q => (p.directWrites).bind fun a => (q.directWrites).map (a ++ ·)
  | .ifNZ _ t f => (t.directWrites).bind fun a => (f.directWrites).map (a ++ ·)
  | .forN _ b => b.directWrites
  | .scanList _ r b => (b.directWrites).map (r :: ·)
  | .lookup _ _ v => some [v]

/-! The unfolding equations of `Program.directWrites` state its meaning, which `brecOn` does not
expose. -/

@[stable_api] lemma Program.directWrites_skip : Program.skip.directWrites = some [] := rfl

@[stable_api] lemma Program.directWrites_assign (r : ℕ) (e : Expr) :
    (Program.assign r e).directWrites = some [r] := rfl

@[stable_api] lemma Program.directWrites_assignInd (eA e : Expr) :
    (Program.assignInd eA e).directWrites = none := rfl

@[stable_api] lemma Program.directWrites_seq (p q : Program) :
    (Program.seq p q).directWrites =
      p.directWrites.bind fun a => q.directWrites.map (a ++ ·) := rfl

@[stable_api] lemma Program.directWrites_ifNZ (c : Expr) (t f : Program) :
    (Program.ifNZ c t f).directWrites =
      t.directWrites.bind fun a => f.directWrites.map (a ++ ·) := rfl

@[stable_api] lemma Program.directWrites_forN (n : Expr) (b : Program) :
    (Program.forN n b).directWrites = b.directWrites := rfl

@[stable_api] lemma Program.directWrites_scanList (xs : List ℕ) (r : ℕ) (b : Program) :
    (Program.scanList xs r b).directWrites = b.directWrites.map (r :: ·) := rfl

@[stable_api] lemma Program.directWrites_lookup (pairs : List (ℕ × ℕ)) (k v : ℕ) :
    (Program.lookup pairs k v).directWrites = some [v] := rfl

/-- A loop preserves register `r` when its body does, from every store. -/
@[stable_api] lemma loopEval_frame (b : Program) (r : ℕ)
    (hb : ∀ σ : Store, b.eval σ r = σ r) : ∀ (k : ℕ) (σ : Store), loopEval b k σ r = σ r := by
  intro k; induction k with
  | zero => intro σ; simp
  | succ k ih => intro σ; rw [loopEval_succ, ih, hb]

/-- A list scan preserves register `r` when its body does and `r` is not the binder. -/
@[stable_api] lemma scanListEval_frame (b : Program) (x r : ℕ) (hx : r ≠ x)
    (hb : ∀ σ : Store, b.eval σ r = σ r) : ∀ (xs : List ℕ) (σ : Store),
    scanListEval b xs x σ r = σ r := by
  intro xs; induction xs with
  | nil => intro σ; simp
  | cons y ys ih => intro σ; rw [scanListEval_cons, ih, hb, writeReg_diff _ _ _ _ hx]

/-- A register outside the syntactic write set is unchanged by evaluation. -/
@[stable_api] lemma Program.eval_frame (p : Program) : ∀ (ws : List ℕ), p.directWrites = some ws →
    ∀ (σ : Store) (r : ℕ), r ∉ ws → p.eval σ r = σ r := by
  induction p with
  | skip => intro _ _ σ r _; simp
  | assign a e =>
    intro ws h σ r hr
    simp only [Program.directWrites, Option.some.injEq] at h; subst h
    rw [eval_assign, writeReg_diff _ _ _ _ (by simpa using hr)]
  | assignInd _ _ => intro _ h; simp [Program.directWrites] at h
  | seq p q ihp ihq =>
    intro ws h σ r hr
    simp only [Program.directWrites, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [List.mem_append, not_or] at hr
    rw [eval_seq, ihq b hb _ r hr.2, ihp a ha σ r hr.1]
  | ifNZ e t f iht ihf =>
    intro ws h σ r hr
    simp only [Program.directWrites, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    simp only [List.mem_append, not_or] at hr
    rw [eval_ifNZ]; split
    · exact iht a ha σ r hr.1
    · exact ihf b hb σ r hr.2
  | forN n b ih =>
    intro ws h σ r hr
    rw [eval_forN]; exact loopEval_frame b r (fun σ' => ih ws h σ' r hr) _ σ
  | scanList xs x b ih =>
    intro ws h σ r hr
    simp only [Program.directWrites, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [List.mem_cons, not_or] at hr
    rw [eval_scanList]; exact scanListEval_frame b x r hr.1 (fun σ' => ih a ha σ' r hr.2) xs σ
  | lookup _ _ v =>
    intro ws h σ r hr
    simp only [Program.directWrites, Option.some.injEq] at h; subst h
    rw [eval_lookup, writeReg_diff _ _ _ _ (by simpa using hr)]

/-- Upper-bound form: every direct write is at most `B`, so registers above `B` are unchanged.
This lets callers bound a program's footprint once and reuse it for every register above it. -/
@[stable_api] lemma Program.eval_frame_of_le {p : Program} {ws : List ℕ} {B : ℕ}
    (h : p.directWrites = some ws) (hw : ∀ w ∈ ws, w ≤ B) (σ : Store) {r : ℕ} (hr : B < r) :
    p.eval σ r = σ r :=
  p.eval_frame ws h σ r fun hmem => absurd (hw r hmem) (by omega)

/-- Lower-bound form: every direct write is at least `B`, so registers below `B` are unchanged. -/
@[stable_api] lemma Program.eval_frame_of_ge {p : Program} {ws : List ℕ} {B : ℕ}
    (h : p.directWrites = some ws) (hw : ∀ w ∈ ws, B ≤ w) (σ : Store) {r : ℕ} (hr : r < B) :
    p.eval σ r = σ r :=
  p.eval_frame ws h σ r fun hmem => absurd (hw r hmem) (by omega)

/-- Predicate form: no direct write satisfies `P`, so every register satisfying `P` is unchanged.
Fits callers that describe the untouched registers by a predicate (a conjunction of `≠`). -/
@[stable_api] lemma Program.eval_frame_of_pred {p : Program} {ws : List ℕ} {P : ℕ → Prop}
    (h : p.directWrites = some ws) (hw : ∀ w ∈ ws, ¬ P w) (σ : Store) {r : ℕ} (hr : P r) :
    p.eval σ r = σ r :=
  p.eval_frame ws h σ r fun hmem => hw r hmem hr

/-- Footprint certificate: the program is analyzable and no direct write satisfies `P`.
The tree-shaped `Avoids` check avoids rebuilding concatenated write lists. Proving it once per
program (typically `(by decide +kernel : p.Avoids P).writesAvoid`) lets every frame lemma about
that program reuse it instead of re-checking the write set. -/
@[stable_api] def Program.WritesAvoid (p : Program) (P : ℕ → Prop) : Prop :=
  ∃ ws, p.directWrites = some ws ∧ ∀ w ∈ ws, ¬ P w

@[stable_api] lemma Program.WritesAvoid.mono {p : Program} {P Q : ℕ → Prop} (h : p.WritesAvoid P)
    (hQ : ∀ r, Q r → P r) : p.WritesAvoid Q :=
  let ⟨ws, hws, hw⟩ := h
  ⟨ws, hws, fun w hmem hq => hw w hmem (hQ w hq)⟩

@[stable_api] lemma Program.WritesAvoid.eval_frame {p : Program} {P : ℕ → Prop} (h : p.WritesAvoid P)
    (σ : Store) {r : ℕ} (hr : P r) : p.eval σ r = σ r :=
  let ⟨ws, hws, hw⟩ := h
  p.eval_frame ws hws σ r fun hmem => hw r hmem hr

@[stable_api] lemma Program.WritesAvoid.loopEval_frame {p : Program} {P : ℕ → Prop} (h : p.WritesAvoid P)
    {r : ℕ} (hr : P r) (k : ℕ) (σ : Store) : loopEval p k σ r = σ r :=
  NPComplete.BoundedWhile.loopEval_frame p r (fun σ' => h.eval_frame σ' hr) k σ

/-- Tree-shaped footprint certificate: no write of the program satisfies `P`.

Syntactic, sound but incomplete: it is `False` on `assignInd` (the destination depends on the
store).  The recursion follows the program tree and has a structurally recursive `Decidable`
instance, so a kernel `decide` checks it in time linear in the program size, without building
the write list that `directWrites` concatenates. -/
@[stable_api] def Program.Avoids (P : ℕ → Prop) : Program → Prop
  | .skip => True
  | .assign r _ => ¬ P r
  | .assignInd _ _ => False
  | .seq p q => p.Avoids P ∧ q.Avoids P
  | .ifNZ _ t f => t.Avoids P ∧ f.Avoids P
  | .forN _ b => b.Avoids P
  | .scanList _ r b => ¬ P r ∧ b.Avoids P
  | .lookup _ _ v => ¬ P v

/-! The unfolding equations of `Program.Avoids` state its meaning, which `brecOn` does not
expose. -/

@[stable_api] lemma Program.avoids_skip (P : ℕ → Prop) : Program.skip.Avoids P ↔ True := Iff.rfl

@[stable_api] lemma Program.avoids_assign (P : ℕ → Prop) (r : ℕ) (e : Expr) :
    (Program.assign r e).Avoids P ↔ ¬ P r := Iff.rfl

@[stable_api] lemma Program.avoids_assignInd (P : ℕ → Prop) (eA e : Expr) :
    (Program.assignInd eA e).Avoids P ↔ False := Iff.rfl

@[stable_api] lemma Program.avoids_seq (P : ℕ → Prop) (p q : Program) :
    (Program.seq p q).Avoids P ↔ p.Avoids P ∧ q.Avoids P := Iff.rfl

@[stable_api] lemma Program.avoids_ifNZ (P : ℕ → Prop) (c : Expr) (t f : Program) :
    (Program.ifNZ c t f).Avoids P ↔ t.Avoids P ∧ f.Avoids P := Iff.rfl

@[stable_api] lemma Program.avoids_forN (P : ℕ → Prop) (n : Expr) (b : Program) :
    (Program.forN n b).Avoids P ↔ b.Avoids P := Iff.rfl

@[stable_api] lemma Program.avoids_scanList (P : ℕ → Prop) (xs : List ℕ) (r : ℕ) (b : Program) :
    (Program.scanList xs r b).Avoids P ↔ ¬ P r ∧ b.Avoids P := Iff.rfl

@[stable_api] lemma Program.avoids_lookup (P : ℕ → Prop) (pairs : List (ℕ × ℕ)) (k v : ℕ) :
    (Program.lookup pairs k v).Avoids P ↔ ¬ P v := Iff.rfl

@[stable_api] instance Program.Avoids.decidable (P : ℕ → Prop) [DecidablePred P] :
    ∀ p : Program, Decidable (p.Avoids P)
  | .skip => inferInstanceAs (Decidable True)
  | .assign r _ => inferInstanceAs (Decidable (¬ P r))
  | .assignInd _ _ => inferInstanceAs (Decidable False)
  | .seq p q => @instDecidableAnd _ _ (Program.Avoids.decidable P p) (Program.Avoids.decidable P q)
  | .ifNZ _ t f =>
    @instDecidableAnd _ _ (Program.Avoids.decidable P t) (Program.Avoids.decidable P f)
  | .forN _ b => Program.Avoids.decidable P b
  | .scanList _ _ b => @instDecidableAnd _ _ inferInstance (Program.Avoids.decidable P b)
  | .lookup _ _ v => inferInstanceAs (Decidable (¬ P v))

@[stable_api] lemma Program.Avoids.mono {p : Program} {P Q : ℕ → Prop} (h : p.Avoids P)
    (hQ : ∀ r, Q r → P r) : p.Avoids Q := by
  induction p with
  | skip => trivial
  | assign r _ => exact fun hq => h (hQ r hq)
  | assignInd _ _ => exact h
  | seq p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | ifNZ _ t f iht ihf => exact ⟨iht h.1, ihf h.2⟩
  | forN _ b ih => exact ih h
  | scanList _ r b ih => exact ⟨fun hq => h.1 (hQ r hq), ih h.2⟩
  | lookup _ _ v => exact fun hq => h (hQ v hq)

@[stable_api] lemma Program.Avoids.eval_frame {p : Program} {P : ℕ → Prop} (h : p.Avoids P)
    (σ : Store) {r : ℕ} (hr : P r) : p.eval σ r = σ r := by
  induction p generalizing σ with
  | skip => simp
  | assign a e =>
    have h' : ¬ P a := h
    rw [eval_assign, writeReg_diff _ _ _ _ (fun hra : r = a => h' (hra ▸ hr))]
  | assignInd _ _ => exact h.elim
  | seq p q ihp ihq => rw [eval_seq, ihq h.2, ihp h.1]
  | ifNZ e t f iht ihf =>
    rw [eval_ifNZ]; split
    · exact iht h.1 σ
    · exact ihf h.2 σ
  | forN n b ih =>
    rw [eval_forN]; exact loopEval_frame b r (fun σ' => ih h σ') _ σ
  | scanList xs x b ih =>
    rw [eval_scanList]
    have h' : ¬ P x := h.1
    exact scanListEval_frame b x r (fun hrx : r = x => h' (hrx ▸ hr)) (fun σ' => ih h.2 σ') xs σ
  | lookup _ _ v =>
    have h' : ¬ P v := h
    rw [eval_lookup, writeReg_diff _ _ _ _ (fun hrv : r = v => h' (hrv ▸ hr))]

@[stable_api] lemma Program.Avoids.loopEval_frame {p : Program} {P : ℕ → Prop} (h : p.Avoids P)
    {r : ℕ} (hr : P r) (k : ℕ) (σ : Store) : loopEval p k σ r = σ r :=
  NPComplete.BoundedWhile.loopEval_frame p r (fun σ' => h.eval_frame σ' hr) k σ

@[stable_api] lemma Program.Avoids.writesAvoid {p : Program} {P : ℕ → Prop} (h : p.Avoids P) :
    p.WritesAvoid P := by
  induction p with
  | skip => exact ⟨[], rfl, by simp⟩
  | assign r _ => exact ⟨[r], rfl, fun w hw => by rw [List.mem_singleton.1 hw]; exact h⟩
  | assignInd _ _ => exact h.elim
  | seq p q ihp ihq =>
    obtain ⟨a, ha, hwa⟩ := ihp h.1
    obtain ⟨b, hb, hwb⟩ := ihq h.2
    refine ⟨a ++ b, by simp [Program.directWrites, ha, hb], ?_⟩
    exact fun w hw => (List.mem_append.1 hw).elim (hwa w) (hwb w)
  | ifNZ _ t f iht ihf =>
    obtain ⟨a, ha, hwa⟩ := iht h.1
    obtain ⟨b, hb, hwb⟩ := ihf h.2
    refine ⟨a ++ b, by simp [Program.directWrites, ha, hb], ?_⟩
    exact fun w hw => (List.mem_append.1 hw).elim (hwa w) (hwb w)
  | forN _ b ih => exact ih h
  | scanList _ r b ih =>
    obtain ⟨a, ha, hwa⟩ := ih h.2
    refine ⟨r :: a, by simp [Program.directWrites, ha], ?_⟩
    exact fun w hw => (List.mem_cons.1 hw).elim (fun e => e ▸ h.1) (hwa w)
  | lookup _ _ v => exact ⟨[v], rfl, fun w hw => by rw [List.mem_singleton.1 hw]; exact h⟩

/-- Static lower bound of an expression.

Only `const`, `add`, and `mul` are followed.  `sub`, `regInd`, and every other constructor
are treated as `0`.  Sound, not complete: the value at a store may be strictly larger. -/
@[stable_api] def Expr.lb : Expr → ℕ
  | .const n => n
  | .add a b => a.lb + b.lb
  | .mul a b => a.lb * b.lb
  | _ => 0

/-! The unfolding equations of `Expr.lb` state its meaning, which `brecOn` does not expose. -/

@[stable_api] lemma Expr.lb_const (n : ℕ) : (Expr.const n).lb = n := rfl

@[stable_api] lemma Expr.lb_reg (r : ℕ) : (Expr.reg r).lb = 0 := rfl

@[stable_api] lemma Expr.lb_regInd (e : Expr) : (Expr.regInd e).lb = 0 := rfl

@[stable_api] lemma Expr.lb_add (a b : Expr) : (Expr.add a b).lb = a.lb + b.lb := rfl

@[stable_api] lemma Expr.lb_sub (a b : Expr) : (Expr.sub a b).lb = 0 := rfl

@[stable_api] lemma Expr.lb_mul (a b : Expr) : (Expr.mul a b).lb = a.lb * b.lb := rfl

@[stable_api] lemma Expr.lb_lt (a b : Expr) : (Expr.lt a b).lb = 0 := rfl

@[stable_api] lemma Expr.lb_eq (a b : Expr) : (Expr.eq a b).lb = 0 := rfl

@[stable_api] lemma Expr.lb_le (e : Expr) (σ : Store) : e.lb ≤ e.eval σ := by
  induction e with
  | add _ _ iha ihb => simp only [Expr.lb, Expr.eval]; omega
  | mul _ _ iha ihb => simp only [Expr.lb, Expr.eval]; exact Nat.mul_le_mul iha ihb
  | const _ => simp [Expr.lb, Expr.eval]
  | _ => simp [Expr.lb]

/-- Tree-shaped certificate that no write lands in `{a | P a ∧ a < B}`.

Same shape as `Avoids`, except an indirect write is accepted when its address expression
has static lower bound at least `B`.  That bound follows only `const`, `add`, and `mul`;
`sub` and `regInd` are treated as `0`, so the check is sound but incomplete.  The protected
range is one-sided (`r < B`): a register at or above `B` is not claimed. -/
@[stable_api] def Program.AvoidsAbove (P : ℕ → Prop) (B : ℕ) : Program → Prop
  | .skip => True
  | .assign r _ => ¬ P r
  | .assignInd eA _ => B ≤ eA.lb
  | .seq p q => p.AvoidsAbove P B ∧ q.AvoidsAbove P B
  | .ifNZ _ t f => t.AvoidsAbove P B ∧ f.AvoidsAbove P B
  | .forN _ b => b.AvoidsAbove P B
  | .scanList _ r b => ¬ P r ∧ b.AvoidsAbove P B
  | .lookup _ _ v => ¬ P v

/-! The unfolding equations of `Program.AvoidsAbove` state its meaning, which `brecOn` does not
expose. -/

@[stable_api] lemma Program.avoidsAbove_skip (P : ℕ → Prop) (B : ℕ) :
    Program.skip.AvoidsAbove P B ↔ True := Iff.rfl

@[stable_api] lemma Program.avoidsAbove_assign (P : ℕ → Prop) (B : ℕ) (r : ℕ) (e : Expr) :
    (Program.assign r e).AvoidsAbove P B ↔ ¬ P r := Iff.rfl

@[stable_api] lemma Program.avoidsAbove_assignInd (P : ℕ → Prop) (B : ℕ) (eA e : Expr) :
    (Program.assignInd eA e).AvoidsAbove P B ↔ B ≤ eA.lb := Iff.rfl

@[stable_api] lemma Program.avoidsAbove_seq (P : ℕ → Prop) (B : ℕ) (p q : Program) :
    (Program.seq p q).AvoidsAbove P B ↔ p.AvoidsAbove P B ∧ q.AvoidsAbove P B := Iff.rfl

@[stable_api] lemma Program.avoidsAbove_ifNZ (P : ℕ → Prop) (B : ℕ) (c : Expr) (t f : Program) :
    (Program.ifNZ c t f).AvoidsAbove P B ↔ t.AvoidsAbove P B ∧ f.AvoidsAbove P B := Iff.rfl

@[stable_api] lemma Program.avoidsAbove_forN (P : ℕ → Prop) (B : ℕ) (n : Expr) (b : Program) :
    (Program.forN n b).AvoidsAbove P B ↔ b.AvoidsAbove P B := Iff.rfl

@[stable_api] lemma Program.avoidsAbove_scanList (P : ℕ → Prop) (B : ℕ) (xs : List ℕ) (r : ℕ)
    (b : Program) : (Program.scanList xs r b).AvoidsAbove P B ↔ ¬ P r ∧ b.AvoidsAbove P B :=
  Iff.rfl

@[stable_api] lemma Program.avoidsAbove_lookup (P : ℕ → Prop) (B : ℕ) (pairs : List (ℕ × ℕ))
    (k v : ℕ) : (Program.lookup pairs k v).AvoidsAbove P B ↔ ¬ P v := Iff.rfl

@[stable_api] instance Program.AvoidsAbove.decidable (P : ℕ → Prop) [DecidablePred P] (B : ℕ) :
    ∀ p : Program, Decidable (p.AvoidsAbove P B)
  | .skip => inferInstanceAs (Decidable True)
  | .assign r _ => inferInstanceAs (Decidable (¬ P r))
  | .assignInd eA _ => inferInstanceAs (Decidable (B ≤ eA.lb))
  | .seq p q =>
    @instDecidableAnd _ _ (Program.AvoidsAbove.decidable P B p)
      (Program.AvoidsAbove.decidable P B q)
  | .ifNZ _ t f =>
    @instDecidableAnd _ _ (Program.AvoidsAbove.decidable P B t)
      (Program.AvoidsAbove.decidable P B f)
  | .forN _ b => Program.AvoidsAbove.decidable P B b
  | .scanList _ _ b =>
    @instDecidableAnd _ _ inferInstance (Program.AvoidsAbove.decidable P B b)
  | .lookup _ _ v => inferInstanceAs (Decidable (¬ P v))

/-- A register satisfying `P` and lying strictly below `B` is unchanged. -/
@[stable_api] lemma Program.AvoidsAbove.eval_frame {p : Program} {P : ℕ → Prop} {B : ℕ}
    (h : p.AvoidsAbove P B) (σ : Store) {r : ℕ} (hr : P r) (hrB : r < B) :
    p.eval σ r = σ r := by
  induction p generalizing σ with
  | skip => simp
  | assign a _ =>
    have h' : ¬ P a := h
    rw [eval_assign, writeReg_diff _ _ _ _ (fun hra : r = a => h' (hra ▸ hr))]
  | assignInd eA _ =>
    have h' : B ≤ eA.lb := h
    have := eA.lb_le σ
    rw [eval_assignInd, writeReg_diff _ _ _ _ (by omega)]
  | seq _ _ ihp ihq => rw [eval_seq, ihq h.2, ihp h.1]
  | ifNZ _ _ _ iht ihf =>
    rw [eval_ifNZ]; split
    · exact iht h.1 σ
    · exact ihf h.2 σ
  | forN _ b ih =>
    rw [eval_forN]; exact loopEval_frame b r (fun σ' => ih h σ') _ σ
  | scanList _ x b ih =>
    rw [eval_scanList]
    have h' : ¬ P x := h.1
    exact scanListEval_frame b x r (fun hrx : r = x => h' (hrx ▸ hr))
      (fun σ' => ih h.2 σ') _ σ
  | lookup _ _ v =>
    have h' : ¬ P v := h
    rw [eval_lookup, writeReg_diff _ _ _ _ (fun hrv : r = v => h' (hrv ▸ hr))]

/-- Iterating a body that avoids `P` below `B` leaves such a register unchanged. -/
@[stable_api] lemma Program.AvoidsAbove.loopEval_frame {p : Program} {P : ℕ → Prop} {B : ℕ}
    (h : p.AvoidsAbove P B) {r : ℕ} (hr : P r) (hrB : r < B) (k : ℕ) (σ : Store) :
    loopEval p k σ r = σ r :=
  NPComplete.BoundedWhile.loopEval_frame p r
    (fun σ' => h.eval_frame σ' hr hrB) k σ

/-- A smaller predicate and a smaller bound are still avoided, so one certificate covers
    every weaker claim. -/
@[stable_api] lemma Program.AvoidsAbove.mono {p : Program} {P Q : ℕ → Prop} {B B' : ℕ}
    (h : p.AvoidsAbove P B) (hQ : ∀ r, Q r → P r) (hB : B' ≤ B) :
    p.AvoidsAbove Q B' := by
  induction p with
  | skip => trivial
  | assign r _ => exact fun hq => h (hQ r hq)
  | assignInd _ _ => exact le_trans hB h
  | seq _ _ ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | ifNZ _ _ _ iht ihf => exact ⟨iht h.1, ihf h.2⟩
  | forN _ _ ih => exact ih h
  | scanList _ r _ ih => exact ⟨fun hq => h.1 (hQ r hq), ih h.2⟩
  | lookup _ _ v => exact fun hq => h (hQ v hq)

/-- An `Avoids` certificate, which rejects every indirect write, is an `AvoidsAbove`
    certificate at every bound, so an existing proof does not have to be rewritten. -/
@[stable_api] lemma Program.Avoids.avoidsAbove {p : Program} {P : ℕ → Prop} (h : p.Avoids P) (B : ℕ) :
    p.AvoidsAbove P B := by
  induction p with
  | skip => trivial
  | assign _ _ => exact h
  | assignInd _ _ => exact h.elim
  | seq _ _ ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | ifNZ _ _ _ iht ihf => exact ⟨iht h.1, ihf h.2⟩
  | forN _ _ ih => exact ih h
  | scanList _ _ _ ih => exact ⟨h.1, ih h.2⟩
  | lookup _ _ _ => exact h

/-- A store predicate that depends only on the registers satisfying `P`: stores agreeing on
`P` agree on the predicate.  `P` is a sufficient support, not necessarily the smallest. -/
@[stable_api] def ReadsOnly (P : ℕ → Prop) (Q : Store → Prop) : Prop :=
  ∀ σ σ', (∀ r, P r → σ' r = σ r) → Q σ → Q σ'

/-- A larger support still suffices. -/
@[stable_api] lemma ReadsOnly.mono {P P' : ℕ → Prop} {Q : Store → Prop} (hP : ∀ r, P r → P' r)
    (h : ReadsOnly P Q) : ReadsOnly P' Q :=
  fun σ σ' he hq => h σ σ' (fun r hr => he r (hP r hr)) hq

/-- A support lying entirely below `B` may be written as its truncation at `B`. -/
@[stable_api] lemma ReadsOnly.of_lt {P : ℕ → Prop} {Q : Store → Prop} {B : ℕ} (hB : ∀ r, P r → r < B)
    (h : ReadsOnly P Q) : ReadsOnly (fun r => P r ∧ r < B) Q :=
  h.mono fun r hp => ⟨hp, hB r hp⟩

/-- A program avoiding the support of `Q` preserves `Q`. -/
@[stable_api] lemma Program.Avoids.preserves {p : Program} {P : ℕ → Prop} {Q : Store → Prop}
    (hp : p.Avoids P) (hQ : ReadsOnly P Q) {σ : Store} (h : Q σ) : Q (p.eval σ) :=
  hQ σ _ (fun _ hr => hp.eval_frame σ hr) h

/-- Like `Program.Avoids.preserves`, for a support truncated below `B`. -/
@[stable_api] lemma Program.AvoidsAbove.preserves {p : Program} {P : ℕ → Prop} {B : ℕ} {Q : Store → Prop}
    (hp : p.AvoidsAbove P B) (hQ : ReadsOnly (fun r => P r ∧ r < B) Q) {σ : Store}
    (h : Q σ) : Q (p.eval σ) :=
  hQ σ _ (fun _ hr => hp.eval_frame σ hr.1 hr.2) h

/-- A program whose writes avoid the support of `Q` preserves `Q`. -/
@[stable_api] lemma Program.WritesAvoid.preserves {p : Program} {P : ℕ → Prop} {Q : Store → Prop}
    (hp : p.WritesAvoid P) (hQ : ReadsOnly P Q) {σ : Store} (h : Q σ) : Q (p.eval σ) :=
  hQ σ _ (fun _ hr => hp.eval_frame σ hr) h

/-- Iterating a body whose direct writes avoid `r` leaves `r` unchanged. -/
@[stable_api] lemma loopEval_frame_of_writes {b : Program} {ws : List ℕ} {r : ℕ}
    (h : b.directWrites = some ws) (hr : r ∉ ws) (k : ℕ) (σ : Store) :
    loopEval b k σ r = σ r :=
  loopEval_frame b r (fun σ' => b.eval_frame ws h σ' r hr) k σ

/-- Upper-bound form of `loopEval_frame_of_writes`. -/
@[stable_api] lemma loopEval_frame_of_le {b : Program} {ws : List ℕ} {B : ℕ}
    (h : b.directWrites = some ws) (hw : ∀ w ∈ ws, w ≤ B) {r : ℕ} (hr : B < r)
    (k : ℕ) (σ : Store) : loopEval b k σ r = σ r :=
  loopEval_frame b r (fun σ' => b.eval_frame_of_le h hw σ' hr) k σ

/-- Lower-bound form of `loopEval_frame_of_writes`. -/
@[stable_api] lemma loopEval_frame_of_ge {b : Program} {ws : List ℕ} {B : ℕ}
    (h : b.directWrites = some ws) (hw : ∀ w ∈ ws, B ≤ w) {r : ℕ} (hr : r < B)
    (k : ℕ) (σ : Store) : loopEval b k σ r = σ r :=
  loopEval_frame b r (fun σ' => b.eval_frame_of_ge h hw σ' hr) k σ

/-- An invariant preserved by one iteration of the body is preserved by any number of them. -/
@[stable_api] lemma loopEval_inv (b : Program) (P : Store → Prop) (hb : ∀ σ, P σ → P (b.eval σ)) :
    ∀ (k : ℕ) (σ : Store), P σ → P (loopEval b k σ) := by
  intro k; induction k with
  | zero => intro σ h; simpa using h
  | succ k ih => intro σ h; rw [loopEval_succ]; exact ih _ (hb σ h)

/-- A body that fixes the store leaves it fixed under any number of iterations. -/
@[stable_api] lemma loopEval_fixed (b : Program) (σ : Store) (h : b.eval σ = σ) (k : ℕ) :
    loopEval b k σ = σ :=
  loopEval_inv b (· = σ) (fun _ hs => by rw [hs, h]) k σ rfl

end NPComplete.BoundedWhile
