module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.RAMToTM.Generic.Api.StageSpec
public import NPComplete.RAMToTM.Generic.Api.ValuesLeOn
public import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
public import NPComplete.RAMToTM.Generic.BitDecode
public import NPComplete.BoundedWhile.Frame
public import Mathlib.Data.Set.Basic

/-!
# Resource-carrying stage combinators

A resource composition chains small stages that carry local value bounds and pinned cell values
from stage to stage: constant assignments seeding control registers, a unary-number decoder
advancing the cursor past a length prefix, and a loop whose visit count is read from the store
(data-dependent, so `StageSpec.forN` with its `n.eval σ = N` cannot apply).  Each of those
shapes is the same across problems — only the register names, the budget arithmetic and the
body's per-visit resource lemma differ — so the skeletons live here and a system supplies the
per-visit facts.

`StageSpec.assign_const_carry` is the seeding step: it carries `ValuesLeOn` and a supported
fact `C` through a constant assignment and adds the new pin.  `StageSpec.decodeUnaryAt` is the
decoder step: cursor/counter growth bounded by the bound register, the carried fact transported
through the frame.  `programBoundedIn_forN_of_invariant` and `StageSpec.forN_le` are the loop
skeletons for a count only bounded by `N`, with the per-visit resource obligations read off an
invariant instead of a fixed iteration count.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BoundedWhile

/-! ## Supported-fact certificates -/

/-- A cell equality reads only its own register. -/
@[construction_api] lemma readsOnly_cell_eq {P : ℕ → Prop} {a v : ℕ} (ha : P a) :
    ReadsOnly P (fun σ => σ a = v) := by
  intro σ σ' he hσ
  exact (he a ha).trans hσ

/-- Two facts reading only the same registers read only those registers, conjunctively. -/
@[construction_api] lemma readsOnly_and {P : ℕ → Prop} {Q Q' : Store → Prop}
    (hQ : ReadsOnly P Q) (hQ' : ReadsOnly P Q') :
    ReadsOnly P (fun σ => Q σ ∧ Q' σ) := by
  intro σ σ' he ⟨hq, hq'⟩
  exact ⟨hQ σ σ' he hq, hQ' σ σ' he hq'⟩

/-! ## Seeding a control register -/

/-- Assigning a constant to a control register while carrying the local value bound and a
supported fact `C` through: the budget cells stay bounded, `C` survives (it reads only
registers other than `r`), and the pin `r = v` is established. -/
@[construction_api] lemma StageSpec.assign_const_carry {B r v : ℕ} {S : Set ℕ} {C : Store → Prop}
    (hr : r ≤ B) (hv : v ≤ B) (hC : ReadsOnly (fun a => a ≠ r) C) :
    StageSpec B (fun ρ => ValuesLeOn B S ρ ∧ C ρ)
      (.assign r (.const v)) {r}
      (fun ρ => ValuesLeOn B S ρ ∧ C ρ ∧ ρ r = v) := by
  refine StageSpec.assign hr (fun ρ _ => hv) ?_
  intro ρ ⟨hvals, hCρ⟩
  refine ⟨valuesLeOn_writeReg hvals hv, hC _ _ (fun a ha => writeReg_diff ρ r v a ha) hCρ,
    writeReg_same ρ r v⟩

/-! ## The runtime-bound unary decoder as a fact-carrying stage -/

/-- `ProgramBoundedIn` for the runtime-bound unary decoder from the two budgets at the entry
store: the bound register indexes the loop, and every visit's step is bounded because the cursor
and the counter grow by at most the loop count. -/
@[construction_api] lemma programBoundedIn_decodeUnaryProgAt_of_budget (B c k d lr : ℕ)
    (σ : Store) (hcc : c ≠ k) (hcd : c ≠ d) (hkd : k ≠ d)
    (hidx : c ≤ B ∧ k ≤ B ∧ d ≤ B ∧ lr ≤ B)
    (hcursor : σ c + σ lr ≤ B) (hcount : σ k + σ lr ≤ B) :
    ProgramBoundedIn B σ (decodeUnaryProgAt c k d (.reg lr)) := by
  unfold decodeUnaryProgAt
  simp only [ProgramBoundedIn, ExprBoundedIn, Expr.eval]
  refine ⟨hidx.2.2.2, fun m hm => ?_⟩
  apply unary_step_bounded_aux B c k d (loopEval (decodeUnaryStep c k d) m σ) hcc hcd
    ⟨hidx.1, hidx.2.1, hidx.2.2.1⟩
  · have hc := loopEval_decodeUnaryStep_cursor_le c k d hcc hcd m σ
    omega
  · have hk := loopEval_decodeUnaryStep_count_le c k d hcc hkd m σ
    omega

/-- The runtime-bound unary decoder as a fact-carrying stage: from a store whose cursor is at
most `cg`, whose counter holds `k0` and whose bound register holds `lrv`, the decoder leaves the
bound register unchanged, grows the cursor by at most `lrv` and the counter by at most `lrv`, all
within the resource bound `B`; the carried fact `C` (reading only registers the decoder does not
write) and the local value bound survive.  The intermediate pin forms of a resource composition
(`ρ c ≤ cg`) cover both a fresh cursor (`cg` the entry value) and an already-advanced one. -/
@[construction_api] lemma StageSpec.decodeUnaryAt {B c k d lr : ℕ} {S : Set ℕ} {C : Store → Prop}
    (cg k0 lrv : ℕ)
    (hcc : c ≠ k) (hcd : c ≠ d) (hkd : k ≠ d)
    (hne : lr ≠ c ∧ lr ≠ k ∧ lr ≠ d)
    (hidx : c ≤ B ∧ k ≤ B ∧ d ≤ B ∧ lr ≤ B)
    (hC : ReadsOnly (fun a => a ≠ c ∧ a ≠ k ∧ a ≠ d) C)
    (hdS : d ∉ S) (hcg : cg + lrv ≤ B) (hk0 : k0 + lrv ≤ B) :
    StageSpec B
      (fun ρ => ValuesLeOn B S ρ ∧ C ρ ∧ ρ c ≤ cg ∧ ρ lr = lrv ∧ ρ k = k0)
      (decodeUnaryProgAt c k d (.reg lr))
      (fun r => r = c ∨ r = k ∨ r = d)
      (fun τ => ValuesLeOn B S τ ∧ C τ ∧ τ lr = lrv ∧ τ c ≤ cg + lrv ∧ τ k ≤ k0 + lrv) := by
  refine StageSpec.of_avoids ?_ (fun ρ hρ => ?_) (fun ρ hρ => ?_)
  · simp [Program.Avoids, decodeUnaryProgAt, decodeUnaryStep]
    refine ⟨?_, ?_⟩ <;> refine ⟨?_, ?_⟩ <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
  · obtain ⟨hvals, hCρ, hcur, hLR, hk⟩ := hρ
    have hframe : ∀ a, a ≠ c → a ≠ k → a ≠ d →
        (decodeUnaryProgAt c k d (.reg lr)).eval ρ a = ρ a :=
      fun a => decodeUnaryProgAt_frame c k d (.reg lr) a ρ
    have hτc : (decodeUnaryProgAt c k d (.reg lr)).eval ρ c ≤ ρ c + ρ lr := by
      unfold decodeUnaryProgAt
      rw [eval_forN, Expr.eval_reg]
      exact loopEval_decodeUnaryStep_cursor_le c k d hcc hcd _ ρ
    have hτk : (decodeUnaryProgAt c k d (.reg lr)).eval ρ k ≤ ρ k + ρ lr := by
      unfold decodeUnaryProgAt
      rw [eval_forN, Expr.eval_reg]
      exact loopEval_decodeUnaryStep_count_le c k d hcc hkd _ ρ
    have hvalsτ : ValuesLeOn B S ((decodeUnaryProgAt c k d (.reg lr)).eval ρ) := by
      intro a ha
      by_cases hca : a = c
      · subst hca; omega
      · by_cases hka : a = k
        · subst hka; omega
        · have hda : a ≠ d := fun h => hdS (h ▸ ha)
          rw [hframe a hca hka hda]
          exact hvals a ha
    refine ⟨hvalsτ, hC _ _ (fun a ha => hframe a ha.1 ha.2.1 ha.2.2) hCρ,
      (hframe lr hne.1 hne.2.1 hne.2.2).trans hLR,
      by omega, by omega⟩
  · obtain ⟨_, _, hcur, hLR, hk⟩ := hρ
    exact programBoundedIn_decodeUnaryProgAt_of_budget B c k d lr ρ hcc hcd hkd hidx
      (by omega) (by omega)

/-! ## Data-dependent-count loops -/

/-- `ProgramBoundedIn` for a `forN` loop whose count is data-dependent: only bounded by `N` at
the entry store, with the invariant `I` established at every visited store and each visit's
resource obligation discharged from `I`.  This is the resource-level counterpart of
`StageSpec.forN` when the entry facts cannot fix `n.eval σ = N`. -/
@[construction_api] lemma programBoundedIn_forN_of_invariant (B N : ℕ) (σ : Store) (n : Expr)
    (body : Program) (I : ℕ → Store → Prop)
    (hn : ExprBoundedIn B σ n) (hcount : n.eval σ ≤ N)
    (hinv : ∀ j ≤ N, I j (loopEval body j σ))
    (hvisit : ∀ j < N, ∀ τ, I j τ → ProgramBoundedIn B τ body) :
    ProgramBoundedIn B σ (.forN n body) :=
  ⟨hn, fun m hm => hvisit m (by omega) _ (hinv m (by omega))⟩

/-- A `forN` loop as a resource-only stage with a data-dependent count: the count is merely
bounded by `N`, the invariant `I` holds at every visited store, the body's writes stay inside
`W`, and the postcondition is trivial (the facts at the final store are read off `I` at the use
site, where the actual visit count is known). -/
@[construction_api] lemma StageSpec.forN_le {B N : ℕ} {P : Store → Prop} {n : Expr}
    {body : Program} {I : ℕ → Store → Prop} {W : Set ℕ}
    (hn : ∀ σ, P σ → ExprBoundedIn B σ n) (hcount : ∀ σ, P σ → n.eval σ ≤ N)
    (hinv : ∀ σ, P σ → ∀ j ≤ N, I j (loopEval body j σ))
    (hA : body.Avoids (fun r => r ∉ W))
    (hvisit : ∀ j < N, ∀ τ, I j τ → ProgramBoundedIn B τ body) :
    StageSpec B P (Program.forN n body) W (fun _ => True) := by
  refine StageSpec.of_avoids hA (fun _ _ => trivial) (fun σ hP => ?_)
  exact programBoundedIn_forN_of_invariant B N σ n body I (hn σ hP) (hcount σ hP)
    (hinv σ hP) hvisit

end NPComplete.RAMToTM
