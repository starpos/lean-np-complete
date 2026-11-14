module

meta import NPComplete.Meta.ApiLayer
public import NPComplete.BoundedWhile.StoreFact
public import NPComplete.BoundedWhile.WritesIn
public import NPComplete.RAMToTM.Generic.Api.SameOff
public import NPComplete.RAMToTM.Generic.Api.BoundedInMono
public import Mathlib.Data.Set.Disjoint

/-!
# Stage contracts

A stage of a construction is usually described by three separate obligations: what it
establishes, what it leaves alone, and that its operands stay within a resource bound.  `StageSpec`
packs them into one statement, so a stage that grows a temporary register inside its reserved
footprint changes nothing above it, and the composition rules (`seq`, `forN`, `frame`) are stated
once, independent of any problem.

The footprint is a set of addresses (`Set ℕ`), so inclusion and disjointness compose by set algebra.
-/

@[expose] public section

open NPComplete.BoundedWhile

namespace NPComplete.RAMToTM

/-- Contract of one stage: from a store satisfying `P`, the program `p` reaches a store satisfying
`Q`, agrees with the starting store outside the footprint `W`, and satisfies `ProgramBoundedIn B`.

What this guarantees is limited.  `W` is a reserved footprint, not an exact write set: the stage
may write less.  `SameOff` compares only the final store with the initial one, so a register
outside `W` may be written during the run as long as it ends with its initial value.
`ProgramBoundedIn B` bounds the written addresses and the operands evaluated along the run; it is
neither a cost bound nor a bound on the values of all registers of the store. -/
@[construction_api] def StageSpec (B : ℕ) (P : Store → Prop) (p : Program) (W : Set ℕ)
    (Q : Store → Prop) : Prop :=
  ∀ σ, P σ → Q (p.eval σ) ∧ SameOff (· ∈ W) σ (p.eval σ) ∧ ProgramBoundedIn B σ p

@[construction_api] lemma StageSpec.seq {B : ℕ} {P M Q : Store → Prop} {W₁ W₂ : Set ℕ}
    {p q : Program} (h₁ : StageSpec B P p W₁ M) (h₂ : StageSpec B M q W₂ Q) :
    StageSpec B P (p.seq q) (W₁ ∪ W₂) Q := by
  intro σ hP
  obtain ⟨hM, hf₁, hb₁⟩ := h₁ σ hP
  obtain ⟨hQ, hf₂, hb₂⟩ := h₂ _ hM
  refine ⟨by simpa [eval_seq] using hQ, ?_, ⟨hb₁, hb₂⟩⟩
  rw [eval_seq]
  exact (hf₁.mono fun r h => Set.mem_union_left W₂ h).trans
    (hf₂.mono fun r h => Set.mem_union_right W₁ h)

@[construction_api] lemma StageSpec.weaken {B : ℕ} {P P' : Store → Prop} {p : Program}
    {W W' : Set ℕ} {Q Q' : Store → Prop} (h : StageSpec B P p W Q) (hP : ∀ σ, P' σ → P σ)
    (hW : W ⊆ W') (hQ : ∀ σ, Q σ → Q' σ) : StageSpec B P' p W' Q' := by
  intro σ hP'
  obtain ⟨hQσ, hf, hb⟩ := h σ (hP σ hP')
  exact ⟨hQ _ hQσ, hf.mono (fun _ hr => hW hr), hb⟩

/-- Raise the resource bound. -/
@[construction_api] lemma StageSpec.mono_bound {B B' : ℕ} {P Q : Store → Prop} {p : Program}
    {W : Set ℕ} (h : StageSpec B P p W Q) (hB : B ≤ B') : StageSpec B' P p W Q := by
  intro σ hP
  obtain ⟨hQ, hf, hb⟩ := h σ hP
  exact ⟨hQ, hf, programBoundedIn_mono p hB hb⟩

/-- A fact with support `S` disjoint from the footprint survives the stage. -/
@[construction_api] lemma StageSpec.frame {B : ℕ} {P Q F : Store → Prop} {W S : Set ℕ}
    {p : Program} (h : StageSpec B P p W Q) (hF : ReadsOnly (· ∈ S) F) (hd : Disjoint S W) :
    StageSpec B (fun σ => P σ ∧ F σ) p W (fun σ => Q σ ∧ F σ) := by
  intro σ ⟨hP, hFσ⟩
  obtain ⟨hQ, hf, hb⟩ := h σ hP
  refine ⟨⟨hQ, hF σ _ (fun r hr => hf r ?_) hFσ⟩, hf, hb⟩
  intro hWr
  exact hd.le_bot ⟨hr, hWr⟩

/-- The frame rule for supported facts: disjointness of the support from the footprint is the only
side condition. -/
@[construction_api] lemma StageSpec.frame_fact {B : ℕ} {P Q : Store → Prop} {W : Set ℕ}
    {p : Program} (h : StageSpec B P p W Q) (F : StoreFact) (hd : Disjoint F.supp W) :
    StageSpec B (fun σ => P σ ∧ F.holds σ) p W (fun σ => Q σ ∧ F.holds σ) :=
  h.frame F.reads_only hd

/-- Iterating a body `N` times under an invariant: the body contract at step `j` moves `I j` to
`I (j + 1)`, each step stays inside its own window `Wj j`, and the loop reserves the union `W`. -/
@[construction_api] lemma StageSpec.forN {B N : ℕ} {P : Store → Prop} {n : Expr} {body : Program}
    {I : ℕ → Store → Prop} {Wj : ℕ → Set ℕ} {W : Set ℕ}
    (hN : ∀ σ, P σ → n.eval σ = N) (hn : ∀ σ, P σ → ExprBoundedIn B σ n)
    (hinit : ∀ σ, P σ → I 0 σ)
    (hbody : ∀ j < N, StageSpec B (I j) body (Wj j) (I (j + 1)))
    (hsub : ∀ j < N, Wj j ⊆ W) :
    StageSpec B P (Program.forN n body) W (I N) := by
  intro σ hP
  have hNσ : n.eval σ = N := hN σ hP
  have hinv : ∀ j ≤ N, I j (loopEval body j σ) := by
    intro j hj
    induction j with
    | zero => simpa using hinit σ hP
    | succ j ih =>
      have hstep := (hbody j (by omega)) (loopEval body j σ) (ih (by omega))
      rw [loopEval_succ_snoc]
      exact hstep.1
  have hwin : ∀ j ≤ N, SameOff (· ∈ W) σ (loopEval body j σ) := by
    intro j hj
    induction j with
    | zero => simpa using SameOff.refl (· ∈ W) σ
    | succ j ih =>
      have hj' : j < N := by omega
      have hstep := (hbody j hj') (loopEval body j σ) (hinv j (by omega))
      rw [loopEval_succ_snoc]
      exact (ih (by omega)).trans (hstep.2.1.mono (hsub j hj'))
  have hbnd : ProgramBoundedIn B σ (Program.forN n body) := by
    rw [programBoundedIn_forN_iff]
    refine ⟨hn σ hP, fun m hm => ?_⟩
    exact ((hbody m (by omega)) (loopEval body m σ) (hinv m (by omega))).2.2
  refine ⟨?_, ?_, hbnd⟩
  · rw [eval_forN, hNσ]
    exact hinv N le_rfl
  · rw [eval_forN, hNσ]
    exact hwin N le_rfl

@[construction_api] lemma StageSpec.assign {B r : ℕ} {P Q : Store → Prop} {e : Expr}
    (hr : r ≤ B) (he : ∀ σ, P σ → ExprBoundedIn B σ e)
    (hQ : ∀ σ, P σ → Q (writeReg σ r (e.eval σ))) :
    StageSpec B P (.assign r e) {r} Q := by
  intro σ hP
  refine ⟨?_, ?_, ⟨hr, he σ hP⟩⟩
  · simpa [eval_assign] using hQ σ hP
  · intro r' hr'
    rw [eval_assign]
    exact writeReg_diff σ r (e.eval σ) r' hr'

/-- A stage whose syntactic writes avoid everything outside `W` (it has no `assignInd`). -/
@[construction_api] lemma StageSpec.of_avoids {B : ℕ} {P Q : Store → Prop} {p : Program}
    {W : Set ℕ} (hA : p.Avoids (fun r => r ∉ W)) (hQ : ∀ σ, P σ → Q (p.eval σ))
    (hb : ∀ σ, P σ → ProgramBoundedIn B σ p) : StageSpec B P p W Q :=
  fun σ hP => ⟨hQ σ hP, fun _ hr => hA.eval_frame σ hr, hb σ hP⟩

/-- A stage whose write destinations, possibly computed from the store by `assignInd`, lie in `W`
whenever the precondition holds.  The resulting contract does not constrain the writes made
during the run, as for every `StageSpec`. -/
@[construction_api] lemma StageSpec.of_writesIn {B : ℕ} {P Q : Store → Prop} {p : Program}
    {W : Set ℕ} (hW : ∀ σ, P σ → WritesIn (· ∈ W) p σ) (hQ : ∀ σ, P σ → Q (p.eval σ))
    (hb : ∀ σ, P σ → ProgramBoundedIn B σ p) : StageSpec B P p W Q :=
  fun σ hP => ⟨hQ σ hP, fun _ hr => WritesIn.eval_frame p σ (hW σ hP) hr, hb σ hP⟩

end NPComplete.RAMToTM
