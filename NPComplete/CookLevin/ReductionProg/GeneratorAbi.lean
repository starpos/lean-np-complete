module

public import NPComplete.CookLevin.ReductionProg.GeneratorEmit
public import NPComplete.RAMToTM.ThreeSat.Problem.ReductionMemoryLayout
public import NPComplete.BoundedWhile.Frame

/-!
# Generator output ABI

The generated bit slice must satisfy the shared reduction-output convention before the program is
used as a reduction. This module fixes the ABI registers and proves how the generator's final store
realizes that convention, separate from clause construction.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Polynomial
open NPComplete.RAMToTM
open NPComplete.RAMToTM.Generic
open NPComplete.BoundedWhile
open NPComplete.BitEncoding (Bits)

/-- The absolute scratch cell that carries the fixed output base to the ABI finalizer. -/
def abiOutBaseReg : ℕ := 2

/-- The absolute scratch cell that carries the output length to the ABI finalizer. -/
def abiOutLenReg : ℕ := 3

/-- The generator followed by the absolute metadata writes required by the caller ABI. -/
noncomputable def generatorProgAbi (p time : Polynomial ℕ) (d : TableauDescriptor)
    (allowedIdx outIdx : List ℕ) : Program :=
  .seq (generatorProgFull p time d allowedIdx outIdx)
    (.seq (Program.assign abiOutBaseReg (.const emitOutputStart))
      (.seq (Program.assign abiOutLenReg
        (.sub (ctlCell emCurJ) (.const emitOutputStart)))
        (finalizeOutputProg abiOutBaseReg abiOutLenReg)))

/-- The metadata writes and finalizer leave the output range itself unchanged. -/
lemma generator_abi_suffix_frame (σ : Store) (r : ℕ)
    (hr0 : r ≠ outAddrCell) (hr1 : r ≠ outLenCell)
    (hrb : r ≠ abiOutBaseReg) (hrl : r ≠ abiOutLenReg) :
    (finalizeOutputProg abiOutBaseReg abiOutLenReg).eval
        ((Program.assign abiOutLenReg
          (.sub (ctlCell emCurJ) (.const emitOutputStart))).eval
          ((Program.assign abiOutBaseReg (.const emitOutputStart)).eval σ)) r = σ r := by
  have hfin := (of_decide_eq_true (by decide +kernel) :
      (finalizeOutputProg abiOutBaseReg abiOutLenReg).Avoids
        (fun r => r ≠ outAddrCell ∧ r ≠ outLenCell)).eval_frame
    ((Program.assign abiOutLenReg
      (.sub (ctlCell emCurJ) (.const emitOutputStart))).eval
      ((Program.assign abiOutBaseReg (.const emitOutputStart)).eval σ)) ⟨hr0, hr1⟩
  calc
    _ = ((Program.assign abiOutLenReg
        (.sub (ctlCell emCurJ) (.const emitOutputStart))).eval
        ((Program.assign abiOutBaseReg (.const emitOutputStart)).eval σ)) r := hfin
    _ = σ r := by
      simp [eval_assign, Expr.eval, writeReg_diff _ abiOutLenReg _ r hrl,
        writeReg_diff _ abiOutBaseReg _ r hrb]

/-- The final ABI suffix preserves the CNF encoding emitted by the generator. -/
lemma generatorProgAbi_bitsAt (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hpref : ∀ a ∈ prefixWord d bits, a < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    BitsAt
      ((generatorProgAbi p time d allowedIdx outIdx).eval (bitInputStore bits))
      emitOutputStart
      (encodeCNF (descTableauCNF (denseLayout (d.numStates + 1)
        ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
        (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length))) := by
  let σ := (generatorProgFull p time d allowedIdx outIdx).eval
    (bitInputStore bits)
  have hfull := generatorProgFull_meets_emitter_output p time d allowedIdx outIdx bits
    hwrite hblank hpref hallowed hout
  intro i hi
  have hframe := generator_abi_suffix_frame σ (emitOutputStart + i)
    (by norm_num [outAddrCell, emitOutputStart])
    (by
      norm_num [outLenCell, emitOutputStart]
      omega)
    (by
      norm_num [abiOutBaseReg, emitOutputStart]
      omega)
    (by
      norm_num [abiOutLenReg, emitOutputStart]
      omega)
  rw [show (generatorProgAbi p time d allowedIdx outIdx).eval (bitInputStore bits) =
      (finalizeOutputProg abiOutBaseReg abiOutLenReg).eval
        ((Program.assign abiOutLenReg
          (.sub (ctlCell emCurJ) (.const emitOutputStart))).eval
          ((Program.assign abiOutBaseReg (.const emitOutputStart)).eval σ)) by
    simp [generatorProgAbi, σ, eval_seq]]
  rw [hframe]
  exact hfull.1 i hi

/-- The final ABI suffix makes the emitted range a `ReductionOutput`. -/
lemma generatorProgAbi_reductionOutput (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hpref : ∀ a ∈ prefixWord d bits, a < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    ReductionOutput
      ((generatorProgAbi p time d allowedIdx outIdx).eval (bitInputStore bits))
      emitOutputStart
      (encodeCNF (descTableauCNF (denseLayout (d.numStates + 1)
        ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
        (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length))).length := by
  let N := bits.length
  let M := setupM p time d allowedIdx N
  let φ := descTableauCNF (denseLayout (d.numStates + 1)
      ((cookWindowPoly p time).eval N) (d.numLetters + 1)) d
    (prefixWord d bits) (p.eval N) allowedIdx outIdx
    ((cookWindowPoly p time).eval N) ((timePoly p time).eval N)
  let out := encodeCNF φ
  let σ := (generatorProgFull p time d allowedIdx outIdx).eval
    (bitInputStore bits)
  have hfull := generatorProgFull_meets_emitter_output p time d allowedIdx outIdx bits
    hwrite hblank hpref hallowed hout
  have hbits : BitsAt σ emitOutputStart out := by
    simpa [σ, out, φ, N] using hfull.1
  have hcur : σ (M + emCurJ) = emitOutputStart + out.length := by
    simpa [σ, out, φ, M, N] using hfull.2.1
  have hroot : σ 0 = M := by
    simpa [σ, M, N] using hfull.2.2
  have hprefixLen : (prefixWord d bits).length ≤ 2 * N + 1 := by
    rw [prefixWord_length]
  have hencode := emitLenPoly_ge_encodeCNF p time d (prefixWord d bits)
    allowedIdx outIdx N hwrite hblank hpref hallowed hout hprefixLen
  have houtE : out.length ≤
      (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval N := by
    simpa [out, φ] using hencode
  have hEM : (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval N < M := by
    dsimp [M]
    unfold setupM
    omega
  have hsafe : emitOutputStart + out.length < M + emCurJ := by
    simp [emitOutputStart, emCurJ]
    omega
  have hs : WriterState σ M emCurJ emitOutputStart out :=
    { root := hroot
      cursor := hcur
      bits := hbits
      start_pos := by norm_num [emitOutputStart]
      safe := hsafe }
  have hro := reductionOutput_of_writerState_abiSuffix
    abiOutBaseReg abiOutLenReg M emCurJ emitOutputStart out σ hs
    (by norm_num [abiOutBaseReg, emitOutputStart])
    (by norm_num [abiOutLenReg, emitOutputStart])
    (by norm_num [abiOutBaseReg, abiOutLenReg])
    (by simp [FinalizeRegsOk, abiOutBaseReg, abiOutLenReg,
      outAddrCell, outLenCell])
    (by norm_num [emitOutputStart])
  simpa [generatorProgAbi, σ, eval_seq] using hro

/-- The physical write log exposes the generator's emitted CNF bits in order. -/
lemma generatorProgAbi_hBits (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hpref : ∀ a ∈ prefixWord d bits, a < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1)
    (log : WriteLog)
    (hlog : (fun a => lookupD log a 0) =
      (generatorProgAbi p time d allowedIdx outIdx).eval (bitInputStore bits)) :
    OutputSlice.physicalBits log
      ⟨emitOutputStart,
        (encodeCNF (descTableauCNF (denseLayout (d.numStates + 1)
          ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
          (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
          ((cookWindowPoly p time).eval bits.length)
          ((timePoly p time).eval bits.length))).length⟩ =
      encodeCNF (descTableauCNF (denseLayout (d.numStates + 1)
        ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
        (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
        ((cookWindowPoly p time).eval bits.length)
        ((timePoly p time).eval bits.length)) := by
  apply physicalBits_of_bitsAt log _ emitOutputStart _
  · intro a
    exact congrFun hlog a
  · exact generatorProgAbi_bitsAt p time d allowedIdx outIdx bits
      hwrite hblank hpref hallowed hout

/-- The output length is bounded by the generator's polynomial envelope. -/
lemma generatorProgAbi_houtLen (p time : Polynomial ℕ)
    (d : TableauDescriptor) (allowedIdx outIdx : List ℕ) (bits : Bits)
    (hwrite : ∀ qi ai qi' bi, d.entry qi ai = .write qi' bi → bi < d.numLetters + 1)
    (hblank : d.blankIdx < d.numLetters + 1)
    (hpref : ∀ a ∈ prefixWord d bits, a < d.numLetters + 1)
    (hallowed : ∀ a ∈ allowedIdx, a < d.numLetters + 1)
    (hout : ∀ a ∈ outIdx, a < d.numLetters + 1) :
    (encodeCNF (descTableauCNF (denseLayout (d.numStates + 1)
      ((cookWindowPoly p time).eval bits.length) (d.numLetters + 1)) d
      (prefixWord d bits) (p.eval bits.length) allowedIdx outIdx
      ((cookWindowPoly p time).eval bits.length)
      ((timePoly p time).eval bits.length))).length ≤
      (emitLenPoly p time (d.numStates + 1) (d.numLetters + 1)
        allowedIdx.length).eval bits.length := by
  apply emitLenPoly_ge_encodeCNF p time d (prefixWord d bits)
    allowedIdx outIdx bits.length hwrite hblank hpref hallowed hout
  rw [prefixWord_length]

end NPComplete.CookLevin
