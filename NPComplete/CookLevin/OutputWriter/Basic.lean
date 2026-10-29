module

public import NPComplete.RAMToTM.Generic.Emit.CanonicalStoreFinalize
public import NPComplete.SAT.ThreeCNFEncoding
public import NPComplete.CookLevin.NatParser

/-!
# Output-buffer append state

Cook-Levin emitters need a common invariant for the growing bit prefix and the
dynamic output cursor. This module establishes that contract and the bit and
unary-natural append operations, so later header and clause writers can compose
writes without repeating the memory-layout proof.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.SAT
open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_assignInd writeReg writeReg_same writeReg_diff
    loopEval loopCost loopCost_le_of_body_le cost_seq cost_forN cost_assignInd eval_forN)
open NPComplete.BitEncoding (Bits encodeNat encodeList encodeNat_length)

/-! ## The append invariant -/

structure WriterState (σ : Store) (M curJ start : ℕ) (pref : Bits) : Prop where
  root : σ 0 = M
  cursor : σ (M + curJ) = start + pref.length
  bits : BitsAt σ start pref
  start_pos : 1 ≤ start
  safe : start + pref.length < M + curJ

def WriterInit (M curJ start : ℕ) (σ : Store) : Prop :=
  WriterState σ M curJ start []

lemma writerInit_mk (M curJ start : ℕ) (σ : Store)
    (hroot : σ 0 = M) (hcursor : σ (M + curJ) = start)
    (hstart : 1 ≤ start)
    (hsafe : start < M + curJ) :
    WriterInit M curJ start σ := by
  refine ⟨hroot, ?_, ?_, hstart, hsafe⟩
  · simpa using hcursor
  · exact bitsAt_nil σ start

/-! ## Unary natural append -/

def writerAppendNatProg (curJ tmpJ : ℕ) (e : Expr) : Program :=
  emitNatProg curJ tmpJ e

lemma writerAppendNatProg_eval
    (M curJ tmpJ start : ℕ) (pref : Bits) (e : Expr) (σ : Store)
    (hcurJ : 1 ≤ curJ) (htmpJ : curJ < tmpJ)
    (hs : WriterState σ M curJ start pref)
    (hroom : start + pref.length + e.eval σ + 1 < M + curJ) :
    WriterState ((writerAppendNatProg curJ tmpJ e).eval σ) M curJ start
      (pref ++ encodeNat (e.eval σ)) := by
  rcases hs with ⟨hroot, hcursor, hbits, hstart, hsafe⟩
  let cur := start + pref.length
  let n := e.eval σ
  have hcur : σ (M + curJ) = cur := by simpa [cur] using hcursor
  have hcur1 : 1 ≤ cur := by
    dsimp [cur]
    omega
  have htmpJ1 : 1 ≤ tmpJ := by omega
  have hsep : cur + e.eval σ < M + curJ := by
    dsimp [cur]
    omega
  have hnat := emitNatProg_eval_state curJ tmpJ M cur e σ hcurJ htmpJ1
    (by omega : curJ ≠ tmpJ) hroot hcur hcur1 hsep
  change WriterState ((emitNatProg curJ tmpJ e).eval σ) M curJ start
      (pref ++ encodeNat (e.eval σ))
  refine ⟨hnat.2.2.2, ?_, ?_, hstart, ?_⟩
  · have hc := hnat.2.1
    convert hc using 1
    all_goals simp [cur, List.length_append, encodeNat_length]
    all_goals omega
  · rw [bitsAt_append]
    refine ⟨?_, hnat.1⟩
    intro i hi
    have hframe := hnat.2.2.1 (start + i)
      (by omega : start + i ≠ M + curJ) (by omega : start + i ≠ M + tmpJ)
      (Or.inl (by dsimp [cur]; omega))
    exact hframe ▸ hbits i hi
  · have := hroom
    simp only [List.length_append, encodeNat_length]
    omega

end NPComplete.CookLevin
