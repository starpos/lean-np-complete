module

public import NPComplete.CookLevin.Verifier.CNFEvalStages
meta import NPComplete.Meta.StageDiscipline
meta import NPComplete.Meta.StageDisciplineCheck

/-!
# Use-site witnesses for the CNF evaluator's carried facts

A fact dropped on its way through the evaluator's fact composition would still build: the
contracts take the fact group as a whole and no downstream consumer reads every piece.
These witnesses read the carried and framed facts at their exit stores — the scratch pin at
the preprocessing exit, the framed pin and block at the stage exit — so losing one of them
breaks the build.  No main construction uses them, so they stay outside the consumer-facing
umbrella and are collected in `Witnesses.lean` instead.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile (Store RegLayout LayoutFact)
open NPComplete.BitEncoding (Bits encodeList)

stage_default boundary

/-- The use site of the carried facts at the preprocessing exit: the scratch pin established at
the composition entry survives the seeding and the count decode and is readable at the loop
entry. -/
lemma decodeCNFEvalDecodedFacts_scratch (B : ℕ) (reg : CNFEvalRole → ℕ) (σ ρ : Store)
    (h : decodeCNFEvalDecodedFacts B reg σ ρ) : ρ (reg .scratch) = σ (reg .scratch) :=
  h.2.1.2

/-! ## Passive facts framed outside the stage contracts

A fact the evaluator neither writes nor carries in any contract — the pin of a role outside
the reserved footprint, or a memory block at or above the layout top — is added from outside
the stage with the frame rule.  The contracts, the facts they carry and the resource core
never see it; only the composition site and the use site mention it. -/

/-- The whole evaluator with the `bound`-role pin framed over it: the evaluator never writes the
`bound` register, so the pin survives although no stage fact carries it. -/
@[stage_contract] lemma decodeCNFEvalProgramAt_stage_of_bounds_frame_bound
    (R : RegLayout CNFEvalRole) (B addr wBase bound : ℕ) (cs : List Clause) (rest : Bits)
    (w : List Bool) (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hbound : cs.length + 1 ≤ bound) (hbound2 : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound) (hwbudget : wBase + bound ≤ B)
    (houterCoarse : addr + bound + bound * (1 + bound + bound * (bound + 1)) +
        2 + 2 * bound + bound * (bound + 1) ≤ B) :
    LayoutStage R B (decodeCNFEvalProgramAtL R.reg)
      ((clauseInvFact R addr 1 wBase bound (encodeList encodeClause cs ++ rest) cs w haddr hb).and
        (LayoutFact.reg .bound bound))
      ((LayoutFact.reg .cnf (if ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0)).and
        (LayoutFact.reg .bound bound))
      (progFoot R) :=
  LayoutStage.frame
    (decodeCNFEvalProgramAt_stage_of_bounds R B addr wBase bound cs rest w haddr hb hWA hbound
      hbound2 hvarbound hwbudget houterCoarse)
    (LayoutFact.reg .bound bound)
    (LayoutFact.reg_foot_sep_iff.2 (by simp [progFoot, progRegs]))

/-- The use site of the framed pin: the `bound` register is readable at the exit store. -/
@[stage_contract] lemma decodeCNFEvalProgramAt_frame_bound_used
    (R : RegLayout CNFEvalRole) (B addr wBase bound : ℕ) (cs : List Clause) (rest : Bits)
    (w : List Bool) (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hbound : cs.length + 1 ≤ bound) (hbound2 : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound) (hwbudget : wBase + bound ≤ B)
    (houterCoarse : addr + bound + bound * (1 + bound + bound * (bound + 1)) +
        2 + 2 * bound + bound * (bound + 1) ≤ B) (σ : Store)
    (hpre : ((clauseInvFact R addr 1 wBase bound (encodeList encodeClause cs ++ rest) cs w haddr
        hb).and (LayoutFact.reg .bound bound)).holds σ) :
    ((decodeCNFEvalProgramAtL R.reg).eval σ) (R.reg .bound) = bound :=
  (((decodeCNFEvalProgramAt_stage_of_bounds_frame_bound R B addr wBase bound cs rest w haddr hb hWA
    hbound hbound2 hvarbound hwbudget houterCoarse).spec σ hpre).1).2

/-- The whole evaluator with a passive memory fact framed over it: the block lies at or above the
layout top, outside every footprint the evaluator reserves, so it survives. -/
@[stage_contract] lemma decodeCNFEvalProgramAt_stage_of_bounds_frame_block
    (R : RegLayout CNFEvalRole) (B addr wBase bound b n : ℕ) (f : ℕ → ℕ) (cs : List Clause)
    (rest : Bits) (w : List Bool) (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hbound : cs.length + 1 ≤ bound) (hbound2 : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound) (hwbudget : wBase + bound ≤ B)
    (houterCoarse : addr + bound + bound * (1 + bound + bound * (bound + 1)) +
        2 + 2 * bound + bound * (bound + 1) ≤ B) (hbmem : R.top ≤ b) :
    LayoutStage R B (decodeCNFEvalProgramAtL R.reg)
      ((clauseInvFact R addr 1 wBase bound (encodeList encodeClause cs ++ rest) cs w haddr hb).and
        (LayoutFact.block b n f hbmem))
      ((LayoutFact.reg .cnf (if ∀ c ∈ cs, clauseSatBool w c = true then 1 else 0)).and
        (LayoutFact.block b n f hbmem))
      (progFoot R) :=
  LayoutStage.frame
    (decodeCNFEvalProgramAt_stage_of_bounds R B addr wBase bound cs rest w haddr hb hWA hbound
      hbound2 hvarbound hwbudget houterCoarse)
    (LayoutFact.block b n f hbmem) ⟨Finset.disjoint_empty_left _, Set.disjoint_empty _⟩

/-- The use site of the framed block: the block cells are readable at the exit store. -/
@[stage_contract] lemma decodeCNFEvalProgramAt_frame_block_used
    (R : RegLayout CNFEvalRole) (B addr wBase bound b n : ℕ) (f : ℕ → ℕ) (cs : List Clause)
    (rest : Bits) (w : List Bool) (haddr : R.top ≤ addr) (hb : R.top ≤ wBase) (hWA : wBase < addr)
    (hbound : cs.length + 1 ≤ bound) (hbound2 : ∀ c ∈ cs, c.lits.length + 1 ≤ bound)
    (hvarbound : ∀ c ∈ cs, ∀ l ∈ c.lits, l.var + 1 ≤ bound) (hwbudget : wBase + bound ≤ B)
    (houterCoarse : addr + bound + bound * (1 + bound + bound * (bound + 1)) +
        2 + 2 * bound + bound * (bound + 1) ≤ B) (hbmem : R.top ≤ b) (σ : Store)
    (hpre : ((clauseInvFact R addr 1 wBase bound (encodeList encodeClause cs ++ rest) cs w haddr
        hb).and (LayoutFact.block b n f hbmem)).holds σ) :
    ∀ k, k < n → ((decodeCNFEvalProgramAtL R.reg).eval σ) (b + k) = f k :=
  fun k hk =>
    (((decodeCNFEvalProgramAt_stage_of_bounds_frame_block R B addr wBase bound b n f cs rest w
      haddr hb hWA hbound hbound2 hvarbound hwbudget houterCoarse hbmem).spec σ hpre).1).2 k hk

#check_stage_discipline all

end NPComplete.CookLevin
