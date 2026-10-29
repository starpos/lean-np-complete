module

public import NPComplete.RAMToTM.Generic.Machine.GenericEmitMasterRam
public import NPComplete.RAMToTM.Generic.Machine.GenericEmitOutputSlice

/-!
# Transporting prep/emit/cleanup's own closing theorems into `master_flipBind`'s space

The RAM-prefix transport lands the master machine at `MasterΛ.prep EmitPrepPhase.checkLen` with `prep`'s local
state canonical — exactly `GenericEmitPrep.prep_run_length_bounded`'s own starting precondition.
Unlike
the RAM-prefix transport, which uses `GenericEmitMasterProg.ramStop` because `Mg`'s own
`checkHead` case is *not* a literal `halt`, `prepProg`/`emitProg`/`emitCleanupProg`'s own `.done`
phase already *is* a literal `halt` (each file's own module docstring notes this — `StmtTransport`'s fixed-exit
requirement), so `StmtTransport.iterate_bind_step_liftStmt` applies to each of them directly, with
`Ml := prepProg _ _`/`emitProg _ _ _`/`emitCleanupProg` and `lf` their own `.done` label — no
`ramStop`-style substitute dispatcher needed. `masterProg_prep_agrees`/`masterProg_emit_agrees`/
`masterProg_cleanup_agrees` from the master dispatcher construction already supply exactly the `hM` hypothesis each transport
needs.

The key embedding detail is that `iterate_bind_step_liftStmt`'s embedding
condition `∀ k, Sg₀ (ιK k) = (Sl₀ k).map (eΓ k)` type-checks `eΓ k`'s codomain against `Γg (ιK k)`
at `instances` transparency, which does not reduce a bare `id k` to `k` — supplying the proof
term as a bare `Equiv.refl`/`simp` call fails even though the statement is true by definition.
`GenericEmitMaster.emitKId`/`emitKIdEquiv` (marked `@[reducible]`) make this type-check; the
embedding condition itself closes with a direct term (`(List.map_id _).symm`), not `simp`.
-/

@[expose] public section

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (Digit MemSym WriteLog lookupD encodeLog natToDigits liftStmt
  iterate_bind_step_liftStmt)
open Turing Turing.TM2.Stmt

variable {p : List Instruction} (hSup : ProgramSupported p)
  (oReg rAddr rDest rOne rLen : Fin (regBound p))

/-- `GenericEmitPrep.prep_run_length_bounded` transported into `master_flipBind`'s space, with
    the bound on the witness step count carried over unchanged
    (`iterate_bind_step_liftStmt` preserves the step count literally). -/
lemma master_prep_run_length_bounded (n : ℕ) (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k))
    (hsf0 : sf0.prep = PrepState.canonical)
    (hLO : rOne ≠ rLen) (hLen : Sg0 (EmitK.base (Kg.reg rLen)) = natToDigits n)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hCopyScratch : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hDiffScratch : Sg0 (EmitK.base (Kg.scratch .diffScratch)) = ([] : List Digit)) :
    ∃ n' sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n']
        (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
      = some ⟨some (MasterΛ.prep EmitPrepPhase.done), sf, Sgf⟩
      ∧ Sgf EmitK.countdown = List.replicate n () ++ Sg0 EmitK.countdown
      ∧ Sgf (EmitK.base (Kg.reg rLen)) = ([] : List Digit)
      ∧ (∀ k : Kg p, k ≠ Kg.reg rLen → Sgf (EmitK.base k) = Sg0 (EmitK.base k))
      ∧ Sgf EmitK.out = Sg0 EmitK.out
      ∧ n' ≤ n * (16 * (2 * (natToDigits n).length + (natToDigits 1).length + 1) + 2) + 1 := by
  have hSubCanon : sf0.prep.sub = ⟨none, none, false⟩ := by rw [hsf0]; rfl
  obtain ⟨n', sfl, Sgl, hbody⟩ :=
    prep_run_length_bounded rLen rOne n Sg0 sf0.prep hLO hSubCanon hLen hOne hWorkRev hCopyScratch
      hLhsOperand hRhsOperand hDiffScratch
  obtain ⟨hrun, hCd, hRLen, _hROne, _hWR, _hCS, _hLO2, _hRO2, _hDS, hFrame, hOut, hnbound⟩ := hbody
  obtain ⟨sf, Sgf, hrun2, hsf, hSgf, -⟩ :=
    iterate_bind_step_liftStmt emitKId emitKIdEquiv MasterΛ.prep MasterState.getPrep MasterState.setPrep
      (prepProg rLen rOne) (masterProg hSup oReg rAddr rDest rOne rLen) Function.injective_id
      getPrep_setPrep setPrep_setPrep setPrep_getPrep n' EmitPrepPhase.checkLen sf0.prep Sg0
      sf0 Sg0 rfl (fun k => (List.map_id (Sg0 k)).symm) EmitPrepPhase.done sfl Sgl rfl
      (fun l hl => masterProg_prep_agrees hSup oReg rAddr rDest rOne rLen l hl) hrun
  have hSgfEq : ∀ k, Sgf k = Sgl k := fun k => (hSgf k).trans (List.map_id (Sgl k))
  refine ⟨n', sf, Sgf, hrun2, (hSgfEq _).trans hCd, (hSgfEq _).trans hRLen, ?_,
    (hSgfEq _).trans hOut, hnbound⟩
  exact fun k hk => (hSgfEq (EmitK.base k)).trans (hFrame k hk)

/-- `GenericEmit.emit_run_length_bounded` transported into `master_flipBind`'s space, with the
    bound on the witness step count carried over unchanged. -/
lemma master_emit_run_length_bounded (addr : ℕ) (log : WriteLog) (rest0 : List Unit)
    (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k)) (hsf0 : sf0.emit = AllEmitState.canonical)
    (hDD : rDest ≠ rAddr) (hOA : rOne ≠ rAddr) (hOD : rOne ≠ rDest)
    (hCd : Sg0 EmitK.countdown = rest0)
    (hAddr : Sg0 (EmitK.base (Kg.reg rAddr)) = natToDigits addr)
    (hMem : Sg0 (EmitK.base Kg.mem) = encodeLog log)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hSc : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hQ : Sg0 (EmitK.base (Kg.scratch .query)) = ([] : List Digit))
    (hQt : Sg0 (EmitK.base (Kg.scratch .queryTmp)) = ([] : List Digit))
    (hLt : Sg0 (EmitK.base (Kg.scratch .logTmp)) = ([] : List MemSym))
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hSumScratch : Sg0 (EmitK.base (Kg.scratch .sumScratch)) = ([] : List Digit))
    (hDest0 : Sg0 (EmitK.base (Kg.reg rDest)) = ([] : List Digit))
    (hBit : ∀ i < rest0.length, lookupD log (addr + i) 0 = 0 ∨ lookupD log (addr + i) 0 = 1) :
    ∃ n sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n]
        (some ⟨some (MasterΛ.emit EmitPhase.checkMore), sf0, Sg0⟩)
      = some ⟨some (MasterΛ.emit EmitPhase.done), sf, Sgf⟩
      ∧ Sgf EmitK.out = (bitsFor log addr rest0).reverse ++ Sg0 EmitK.out
      ∧ (∀ k : Kg p, k ≠ Kg.reg rAddr → k ≠ Kg.reg rDest → Sgf (EmitK.base k) = Sg0 (EmitK.base k))
      ∧ Sgf (EmitK.base (Kg.reg rDest)) = ([] : List Digit)
      ∧ Sgf (EmitK.base (Kg.reg rAddr)) = natToDigits (addr + rest0.length)
      ∧ Sgf EmitK.countdown = ([] : List Unit)
      ∧ n ≤ rest0.length *
          (32 * ((encodeLog log).length + (natToDigits (addr + rest0.length)).length + 1) ^ 2
            + 16 * (2 * (natToDigits (addr + rest0.length)).length + (natToDigits 1).length
                + bitLen (addr + rest0.length) + bitLen 1 + 1)
            + 6) + 1 := by
  have heq : sf0.emit.load.equal = true := by rw [hsf0]; rfl
  have hAddCanon : sf0.emit.add = ⟨none, none, false⟩ := by rw [hsf0]; rfl
  obtain ⟨n, sfl, Sgl, hbody⟩ :=
    emit_run_length_bounded rAddr rDest rOne addr log rest0 Sg0 sf0.emit hDD hOA hOD hCd hAddr hMem
      hOne hSc hQ hQt hLt hWorkRev hLhsOperand hRhsOperand hSumScratch hDest0 heq hAddCanon hBit
  obtain ⟨hrun, hOut, hRAddrf, _hMem, _hOne, _hSc, _hQ, _hQt, _hLt, _hWorkRev,
    _hLhsOperand, _hRhsOperand, _hSumScratch, hFrame, hDestf, hCdf, hnbound⟩ := hbody
  obtain ⟨sf, Sgf, hrun2, hsf, hSgf, -⟩ :=
    iterate_bind_step_liftStmt emitKId emitKIdEquiv MasterΛ.emit MasterState.getEmit MasterState.setEmit
      (emitProg rAddr rDest rOne) (masterProg hSup oReg rAddr rDest rOne rLen)
      Function.injective_id getEmit_setEmit setEmit_setEmit setEmit_getEmit n
      EmitPhase.checkMore sf0.emit Sg0 sf0 Sg0 rfl (fun k => (List.map_id (Sg0 k)).symm)
      EmitPhase.done sfl Sgl rfl
      (fun l hl => masterProg_emit_agrees hSup oReg rAddr rDest rOne rLen l hl) hrun
  have hSgfEq : ∀ k, Sgf k = Sgl k := fun k => (hSgf k).trans (List.map_id (Sgl k))
  refine ⟨n, sf, Sgf, hrun2, (hSgfEq _).trans hOut, ?_, (hSgfEq _).trans hDestf,
    (hSgfEq _).trans hRAddrf, (hSgfEq _).trans hCdf, hnbound⟩
  exact fun k hkA hkD => (hSgfEq (EmitK.base k)).trans (hFrame k hkA hkD)

/-- `masterProg`'s `.cleanup` case lifts `emitCleanupProg` verbatim at *every* label including
    `done` (`masterProg_cleanup_agrees` has no exception, unlike the `.ram`/`.prep`/`.emit`
    cases) — so `EmitCleanupPhase.done`'s own literal `halt` (`emitCleanupProg`'s module
    docstring) lifts to a literal `halt` at the master level too (`StmtTransport.liftStmt`'s
    `halt => halt` case), one step short of `master_cleanup_run`'s own final `l = none`. -/
lemma master_flipBind_cleanup_done (var : MasterState p) (Sg : ∀ k, List (EmitΓ p k)) :
    master_flipBind hSup oReg rAddr rDest rOne rLen
        (some ⟨some (MasterΛ.cleanup EmitCleanupPhase.done), var, Sg⟩)
       = some ⟨none, MasterState.canonical, Sg⟩ := by
  show (Turing.TM2.step (masterProg hSup oReg rAddr rDest rOne rLen))
      ⟨some (MasterΛ.cleanup EmitCleanupPhase.done), var, Sg⟩ = _
  simp [masterProg]

/-- `GenericEmitCleanup.flipBindEmitCleanup_run_to_done` transported into `master_flipBind`'s space: from
    `MasterΛ.cleanup (EmitCleanupPhase.drainReg 0)`, `master_flipBind` reaches a genuine halt
    (`l = none`) with `EmitK.out` exactly as `flipBindEmitCleanup_run_to_done` itself guarantees
    (untouched). -/
lemma master_cleanup_run (regs : Fin (regBound p) → ℕ) (m0 : List MemSym)
    (copyc queryc queryTmpc : List Digit) (logTmpc : List MemSym)
    (workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc
      prologueWorkc : List Digit) (io0 : List Bool) (cd0 : List Unit)
    (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k))
    (hReg : ∀ i : Fin (regBound p), Sg0 (EmitK.base (Kg.reg i)) = natToDigits (regs i))
    (hMem : Sg0 (EmitK.base Kg.mem) = m0)
    (hCopy : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = copyc)
    (hQuery : Sg0 (EmitK.base (Kg.scratch .query)) = queryc)
    (hQueryTmp : Sg0 (EmitK.base (Kg.scratch .queryTmp)) = queryTmpc)
    (hLogTmp : Sg0 (EmitK.base (Kg.scratch .logTmp)) = logTmpc)
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = workRevc)
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = lhsOperandc)
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = rhsOperandc)
    (hSumScratch : Sg0 (EmitK.base (Kg.scratch .sumScratch)) = sumScratchc)
    (hDiffScratch : Sg0 (EmitK.base (Kg.scratch .diffScratch)) = diffScratchc)
    (hPrologueCounter : Sg0 (EmitK.base (Kg.scratch .prologueCounter)) = prologueCounterc)
    (hPrologueWork : Sg0 (EmitK.base (Kg.scratch .prologueWork)) = prologueWorkc)
    (hIo : Sg0 (EmitK.base Kg.io) = io0) (hCd : Sg0 EmitK.countdown = cd0) :
    ∃ n sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n]
        (some ⟨some (MasterΛ.cleanup (EmitCleanupPhase.drainReg ⟨0, by omega⟩)), sf0, Sg0⟩)
      = some ⟨none, sf, Sgf⟩
      ∧ Sgf EmitK.out = Sg0 EmitK.out := by
  obtain ⟨n, var', Sgl, hrun, _hReg', _hMem', _hScr', _hIo', _hCd', hOut'⟩ :=
    flipBindEmitCleanup_run_to_done regs m0 copyc queryc queryTmpc logTmpc workRevc lhsOperandc
      rhsOperandc sumScratchc diffScratchc prologueCounterc prologueWorkc io0 cd0 sf0.cleanup Sg0
      hReg hMem hCopy hQuery hQueryTmp hLogTmp hWorkRev hLhsOperand hRhsOperand hSumScratch
      hDiffScratch hPrologueCounter hPrologueWork hIo hCd
  obtain ⟨sf, Sgf, hrun2, hsf, hSgf, -⟩ :=
    iterate_bind_step_liftStmt emitKId emitKIdEquiv MasterΛ.cleanup MasterState.getCleanup
      MasterState.setCleanup emitCleanupProg (masterProg hSup oReg rAddr rDest rOne rLen)
      Function.injective_id getCleanup_setCleanup setCleanup_setCleanup setCleanup_getCleanup n
      (EmitCleanupPhase.drainReg ⟨0, by omega⟩) sf0.cleanup Sg0 sf0 Sg0 rfl
      (fun k => (List.map_id (Sg0 k)).symm) EmitCleanupPhase.done var' Sgl rfl
       (fun l hl => masterProg_cleanup_agrees hSup oReg rAddr rDest rOne rLen l hl) hrun
  have hSgfEq : ∀ k, Sgf k = Sgl k := fun k => (hSgf k).trans (List.map_id (Sgl k))
  have hrun2' : (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n]
      (some ⟨some (MasterΛ.cleanup (EmitCleanupPhase.drainReg ⟨0, by omega⟩)), sf0, Sg0⟩)
    = some ⟨some (MasterΛ.cleanup EmitCleanupPhase.done), sf, Sgf⟩ := hrun2
  refine ⟨n + 1, MasterState.canonical, Sgf, ?_, (hSgfEq _).trans hOut'⟩
  rw [show n + 1 = 1 + n from by omega, Function.iterate_add_apply, hrun2', Function.iterate_one]
  exact master_flipBind_cleanup_done hSup oReg rAddr rDest rOne rLen sf Sgf

/-- Quantitative companion to `master_cleanup_run`: same statement, plus a bound on the witness
    step count — `flipBindEmitCleanup_run_to_done_bound`'s bound (using a uniform register-content-length
    cap `M`, `GenericEmitCleanup.lean`'s docstring) plus the final `done → halt` step. -/
lemma master_cleanup_run_bound (regs : Fin (regBound p) → ℕ) (M : ℕ)
    (hM : ∀ i : Fin (regBound p), (natToDigits (regs i)).length ≤ M) (m0 : List MemSym)
    (copyc queryc queryTmpc : List Digit) (logTmpc : List MemSym)
    (workRevc lhsOperandc rhsOperandc sumScratchc diffScratchc prologueCounterc
      prologueWorkc : List Digit) (io0 : List Bool) (cd0 : List Unit)
    (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k))
    (hReg : ∀ i : Fin (regBound p), Sg0 (EmitK.base (Kg.reg i)) = natToDigits (regs i))
    (hMem : Sg0 (EmitK.base Kg.mem) = m0)
    (hCopy : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = copyc)
    (hQuery : Sg0 (EmitK.base (Kg.scratch .query)) = queryc)
    (hQueryTmp : Sg0 (EmitK.base (Kg.scratch .queryTmp)) = queryTmpc)
    (hLogTmp : Sg0 (EmitK.base (Kg.scratch .logTmp)) = logTmpc)
    (hWorkRev : Sg0 (EmitK.base (Kg.scratch .workRev)) = workRevc)
    (hLhsOperand : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = lhsOperandc)
    (hRhsOperand : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = rhsOperandc)
    (hSumScratch : Sg0 (EmitK.base (Kg.scratch .sumScratch)) = sumScratchc)
    (hDiffScratch : Sg0 (EmitK.base (Kg.scratch .diffScratch)) = diffScratchc)
    (hPrologueCounter : Sg0 (EmitK.base (Kg.scratch .prologueCounter)) = prologueCounterc)
    (hPrologueWork : Sg0 (EmitK.base (Kg.scratch .prologueWork)) = prologueWorkc)
    (hIo : Sg0 (EmitK.base Kg.io) = io0) (hCd : Sg0 EmitK.countdown = cd0) :
    ∃ n sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n]
        (some ⟨some (MasterΛ.cleanup (EmitCleanupPhase.drainReg ⟨0, by omega⟩)), sf0, Sg0⟩)
     = some ⟨none, sf, Sgf⟩
       ∧ sf = MasterState.canonical
       ∧ (∀ i : Fin (regBound p), Sgf (EmitK.base (Kg.reg i)) = [])
       ∧ Sgf (EmitK.base Kg.mem) = []
       ∧ (∀ sk : ScratchKind, Sgf (EmitK.base (Kg.scratch sk)) = [])
       ∧ Sgf (EmitK.base Kg.io) = []
       ∧ Sgf EmitK.countdown = []
       ∧ Sgf EmitK.out = Sg0 EmitK.out
      ∧ n ≤ (cd0.length + 1) + ((io0.length + 1) +
            ((prologueWorkc.length + 1 + (prologueCounterc.length + 1) +
                (diffScratchc.length + 1) + (sumScratchc.length + 1) +
                (rhsOperandc.length + 1) + (lhsOperandc.length + 1) + (workRevc.length + 1) +
                (logTmpc.length + 1) + (queryTmpc.length + 1) + (queryc.length + 1) +
                (copyc.length + 1)) +
              ((m0.length + 1) + (regBound p * (M + 1) + 1)))) + 1 := by
  obtain ⟨n, var', Sgl, hrun, hReg', hMem', hScr', hIo', hCd', hOut', hnbound⟩ :=
    flipBindEmitCleanup_run_to_done_bound regs M hM m0 copyc queryc queryTmpc logTmpc workRevc lhsOperandc
      rhsOperandc sumScratchc diffScratchc prologueCounterc prologueWorkc io0 cd0 sf0.cleanup Sg0
      hReg hMem hCopy hQuery hQueryTmp hLogTmp hWorkRev hLhsOperand hRhsOperand hSumScratch
      hDiffScratch hPrologueCounter hPrologueWork hIo hCd
  obtain ⟨sf, Sgf, hrun2, hsf, hSgf, -⟩ :=
    iterate_bind_step_liftStmt emitKId emitKIdEquiv MasterΛ.cleanup MasterState.getCleanup
      MasterState.setCleanup emitCleanupProg (masterProg hSup oReg rAddr rDest rOne rLen)
      Function.injective_id getCleanup_setCleanup setCleanup_setCleanup setCleanup_getCleanup n
      (EmitCleanupPhase.drainReg ⟨0, by omega⟩) sf0.cleanup Sg0 sf0 Sg0 rfl
      (fun k => (List.map_id (Sg0 k)).symm) EmitCleanupPhase.done var' Sgl rfl
       (fun l hl => masterProg_cleanup_agrees hSup oReg rAddr rDest rOne rLen l hl) hrun
  have hSgfEq : ∀ k, Sgf k = Sgl k := fun k => (hSgf k).trans (List.map_id (Sgl k))
  have hrun2' : (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n]
      (some ⟨some (MasterΛ.cleanup (EmitCleanupPhase.drainReg ⟨0, by omega⟩)), sf0, Sg0⟩)
    = some ⟨some (MasterΛ.cleanup EmitCleanupPhase.done), sf, Sgf⟩ := hrun2
  refine ⟨n + 1, MasterState.canonical, Sgf, ?_, rfl, ?_, ?_, ?_, ?_, ?_,
    (hSgfEq _).trans hOut', by omega⟩
  · rw [show n + 1 = 1 + n from by omega, Function.iterate_add_apply, hrun2',
      Function.iterate_one]
    exact master_flipBind_cleanup_done hSup oReg rAddr rDest rOne rLen sf Sgf
  · intro i; exact (hSgfEq _).trans (hReg' i)
  · exact (hSgfEq _).trans hMem'
  · intro sk; exact (hSgfEq _).trans (hScr' sk)
  · exact (hSgfEq _).trans hIo'
  · exact (hSgfEq _).trans hCd'

/-- The register contents `master_run_bound` expects once prep and emit have run: `rLen` is
    drained, `rAddr` has advanced by the `n` emitted bits, `rDest` is empty again, and every
    other register is untouched. -/
def masterRunBoundRegs (addr n : ℕ) (regs0 : Fin (regBound p) → ℕ) : Fin (regBound p) → ℕ :=
  fun i => if i = rLen then 0 else if i = rAddr then addr + n else if i = rDest then 0
    else regs0 i

/-- `master_run_bound`: `masterRunBoundRegs` stays within the uniform register-length cap `M`,
    which is what `master_cleanup_run_bound` needs. -/
lemma masterRunBoundRegs_length_le (addr n : ℕ) (regs0 : Fin (regBound p) → ℕ) (M : ℕ)
    (hM0 : ∀ i : Fin (regBound p), (natToDigits (regs0 i)).length ≤ M)
    (hMaddr : (natToDigits (addr + n)).length ≤ M) (i : Fin (regBound p)) :
    (natToDigits (masterRunBoundRegs rAddr rDest rLen addr n regs0 i)).length ≤ M := by
  unfold masterRunBoundRegs
  split_ifs
  · simp [natToDigits_zero]
  · exact hMaddr
  · simp [natToDigits_zero]
  · exact hM0 i

/-- `master_run_bound`: after prep and emit, every register stack holds the digits of
    `masterRunBoundRegs`. Combines prep's frame (everything but `rLen`) with emit's frame
    (everything but `rAddr`/`rDest`) and the three registers they rewrite. -/
lemma master_run_bound_reg_digits (hAL : rAddr ≠ rLen) (hDL : rDest ≠ rLen)
    (n addr : ℕ) (regs0 : Fin (regBound p) → ℕ)
    (Sg0 Sg1 Sg2 : ∀ k, List (EmitΓ p k))
    (hRegs0 : ∀ i : Fin (regBound p), i ≠ rLen → i ≠ rAddr → i ≠ rDest →
      Sg0 (EmitK.base (Kg.reg i)) = natToDigits (regs0 i))
    (hRLen1 : Sg1 (EmitK.base (Kg.reg rLen)) = ([] : List Digit))
    (hFrame1 : ∀ k : Kg p, k ≠ Kg.reg rLen → Sg1 (EmitK.base k) = Sg0 (EmitK.base k))
    (hFrame2 : ∀ k : Kg p, k ≠ Kg.reg rAddr → k ≠ Kg.reg rDest →
      Sg2 (EmitK.base k) = Sg1 (EmitK.base k))
    (hDestf2 : Sg2 (EmitK.base (Kg.reg rDest)) = ([] : List Digit))
    (hRAddrf2 : Sg2 (EmitK.base (Kg.reg rAddr)) = natToDigits (addr + n)) (i : Fin (regBound p)) :
    Sg2 (EmitK.base (Kg.reg i)) = natToDigits (masterRunBoundRegs rAddr rDest rLen addr n regs0 i) := by
  unfold masterRunBoundRegs
  split_ifs with h1 h2 h3
  · subst h1
    exact (hFrame2 _ (fun h => hAL.symm (by injection h))
      (fun h => hDL.symm (by injection h))).trans hRLen1
  · subst h2
    exact hRAddrf2
  · subst h3
    exact hDestf2
  · exact ((hFrame2 _ (fun h => h2 (by injection h)) (fun h => h3 (by injection h))).trans
      (hFrame1 _ (fun h => h1 (by injection h)))).trans (hRegs0 i h1 h2 h3)

/-- `master_run_bound`, up to the end of emit: prep and emit chained from the start state, with
    every scratch stack empty on entry. Returns the state at `MasterΛ.emit EmitPhase.done` in the
    shape `master_cleanup_run_bound` consumes (registers as `masterRunBoundRegs`, all scratch,
    `io` and `countdown` empty), the emitted `out`, and the summed prep/emit step bound. -/
lemma master_run_bound_to_emit_done (hLO : rOne ≠ rLen) (hAL : rAddr ≠ rLen)
    (hDL : rDest ≠ rLen) (hDD : rDest ≠ rAddr) (hOA : rOne ≠ rAddr) (hOD : rOne ≠ rDest)
    (n addr : ℕ) (log : WriteLog) (regs0 : Fin (regBound p) → ℕ)
    (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k)) (hsf0 : sf0.prep = PrepState.canonical)
    (hLen : Sg0 (EmitK.base (Kg.reg rLen)) = natToDigits n)
    (hAddr : Sg0 (EmitK.base (Kg.reg rAddr)) = natToDigits addr)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hDest0 : Sg0 (EmitK.base (Kg.reg rDest)) = ([] : List Digit))
    (hRegs0 : ∀ i : Fin (regBound p), i ≠ rLen → i ≠ rAddr → i ≠ rDest →
      Sg0 (EmitK.base (Kg.reg i)) = natToDigits (regs0 i))
    (hMem0 : Sg0 (EmitK.base Kg.mem) = encodeLog log)
    (hCd0 : Sg0 EmitK.countdown = ([] : List Unit)) (hOut0 : Sg0 EmitK.out = [])
    (hScr0 : ∀ sk : ScratchKind, Sg0 (EmitK.base (Kg.scratch sk)) = [])
    (hIo0 : Sg0 (EmitK.base Kg.io) = ([] : List Bool))
    (hBit : ∀ i < n, lookupD log (addr + i) 0 = 0 ∨ lookupD log (addr + i) 0 = 1) :
    ∃ n' sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n']
        (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
      = some ⟨some (MasterΛ.emit EmitPhase.done), sf, Sgf⟩
      ∧ Sgf EmitK.out = (OutputSlice.physicalBits log ⟨addr, n⟩).reverse
      ∧ (∀ i : Fin (regBound p),
          Sgf (EmitK.base (Kg.reg i)) = natToDigits (masterRunBoundRegs rAddr rDest rLen addr n regs0 i))
      ∧ Sgf (EmitK.base Kg.mem) = encodeLog log
      ∧ (∀ sk : ScratchKind, Sgf (EmitK.base (Kg.scratch sk)) = [])
      ∧ Sgf (EmitK.base Kg.io) = ([] : List Bool)
      ∧ Sgf EmitK.countdown = ([] : List Unit)
      ∧ n' ≤ (n * (16 * (2 * (natToDigits n).length + (natToDigits 1).length + 1) + 2) + 1) +
          (n * (32 * ((encodeLog log).length + (natToDigits (addr + n)).length + 1) ^ 2
              + 16 * (2 * (natToDigits (addr + n)).length + (natToDigits 1).length
                  + bitLen (addr + n) + bitLen 1 + 1)
              + 6) + 1) + 1 := by
  have hneAL : (Kg.reg rAddr : Kg p) ≠ Kg.reg rLen := fun h => hAL (by injection h)
  have hneDL : (Kg.reg rDest : Kg p) ≠ Kg.reg rLen := fun h => hDL (by injection h)
  have hneOL : (Kg.reg rOne : Kg p) ≠ Kg.reg rLen := fun h => hLO (by injection h)
  obtain ⟨n1, sf1, Sg1, hrun1, hCd1, hRLen1, hFrame1, hOut1, hn1⟩ :=
    master_prep_run_length_bounded hSup oReg rAddr rDest rOne rLen n sf0 Sg0 hsf0 hLO hLen hOne
      (hScr0 .workRev) (hScr0 .copyScratch) (hScr0 .lhsOperand) (hScr0 .rhsOperand)
      (hScr0 .diffScratch)
  have hScr1 : ∀ sk : ScratchKind, Sg1 (EmitK.base (Kg.scratch sk)) = [] :=
    fun sk => (hFrame1 _ (by simp)).trans (hScr0 sk)
  have hCd1' : Sg1 EmitK.countdown = List.replicate n () := by rw [hCd1, hCd0, List.append_nil]
  have hBit' : ∀ i < (List.replicate n ()).length, lookupD log (addr + i) 0 = 0 ∨
      lookupD log (addr + i) 0 = 1 := by
    rw [List.length_replicate]; exact hBit
  obtain ⟨n2, sf2, Sg2, hrun2, hOut2, hFrame2, hDestf2, hRAddrf2, hCdf2, hn2⟩ :=
    master_emit_run_length_bounded hSup oReg rAddr rDest rOne rLen addr log (List.replicate n ())
      (MasterState.setEmit sf1 AllEmitState.canonical) Sg1 rfl hDD hOA hOD hCd1'
      ((hFrame1 _ hneAL).trans hAddr) ((hFrame1 _ (by simp)).trans hMem0)
      ((hFrame1 _ hneOL).trans hOne) (hScr1 .copyScratch) (hScr1 .query) (hScr1 .queryTmp)
      (hScr1 .logTmp) (hScr1 .workRev) (hScr1 .lhsOperand) (hScr1 .rhsOperand)
      (hScr1 .sumScratch) ((hFrame1 _ hneDL).trans hDest0) hBit'
  rw [List.length_replicate] at hn2 hRAddrf2
  have hA : (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n1 + 1]
      (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
    = some ⟨some (MasterΛ.emit EmitPhase.checkMore),
        MasterState.setEmit sf1 AllEmitState.canonical, Sg1⟩ := by
    rw [Function.iterate_succ_apply', hrun1]
    exact master_flipBind_prep_done hSup oReg rAddr rDest rOne rLen sf1 Sg1
  have hPreserve : ∀ k : Kg p, k ≠ Kg.reg rLen → k ≠ Kg.reg rAddr → k ≠ Kg.reg rDest →
      Sg2 (EmitK.base k) = Sg0 (EmitK.base k) :=
    fun k hL hA hD => (hFrame2 k hA hD).trans (hFrame1 k hL)
  refine ⟨n2 + (n1 + 1), sf2, Sg2, ?_, ?_, ?_, ?_, ?_, ?_, hCdf2, by omega⟩
  · rw [Function.iterate_add_apply, hA, hrun2]
  · rw [hOut2, hOut1, hOut0, List.append_nil]
    rfl
  · exact master_run_bound_reg_digits rAddr rDest rLen hAL hDL n addr regs0 Sg0 Sg1 Sg2 hRegs0
      hRLen1 hFrame1 hFrame2 hDestf2 hRAddrf2
  · exact (hFrame2 _ (by simp) (by simp)).trans ((hFrame1 _ (by simp)).trans hMem0)
  · exact fun sk => (hPreserve _ (by simp) (by simp) (by simp)).trans (hScr0 sk)
  · exact (hPreserve _ (by simp) (by simp) (by simp)).trans hIo0

/-- The full master-machine correctness composition, from
    `MasterΛ.prep EmitPrepPhase.checkLen` with `prep` canonical (the RAM-prefix transport's conclusion) all
    the way to a genuine halt. The incoming stack's
    register/scratch/mem/`out`/`countdown` values are taken as an explicit *ABI witness*
    (`hLen`/`hAddr`/`hOne`/`hDest0`/`hRegs0`/`hMem0`/`hCd0`/`hOut0`/`hIo0` and the
    scratch hypotheses) rather
    than derived from `BoundedWhileDecider`/RAM semantics — connecting these facts to a concrete
    RAM computation is the caller's responsibility: the same design `prep_run_length_bounded`/
    `emit_run_length_bounded` themselves already use for *their* register-value hypotheses.
    The proof chains
    `master_run_bound_to_emit_done` (prep and emit, with every scratch stack empty) →
    `master_flipBind_emit_done` → `master_cleanup_run`. -/
lemma master_run_to_halt (hLO : rOne ≠ rLen) (hAL : rAddr ≠ rLen) (hDL : rDest ≠ rLen)
    (hDD : rDest ≠ rAddr) (hOA : rOne ≠ rAddr) (hOD : rOne ≠ rDest)
    (n addr : ℕ) (log : WriteLog) (regs0 : Fin (regBound p) → ℕ)
    (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k)) (hsf0 : sf0.prep = PrepState.canonical)
    (hLen : Sg0 (EmitK.base (Kg.reg rLen)) = natToDigits n)
    (hAddr : Sg0 (EmitK.base (Kg.reg rAddr)) = natToDigits addr)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hDest0 : Sg0 (EmitK.base (Kg.reg rDest)) = ([] : List Digit))
    (hRegs0 : ∀ i : Fin (regBound p), i ≠ rLen → i ≠ rAddr → i ≠ rDest →
      Sg0 (EmitK.base (Kg.reg i)) = natToDigits (regs0 i))
    (hMem0 : Sg0 (EmitK.base Kg.mem) = encodeLog log)
    (hCd0 : Sg0 EmitK.countdown = ([] : List Unit)) (hOut0 : Sg0 EmitK.out = [])
    (hWorkRev0 : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hCopyScratch0 : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hLhsOperand0 : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand0 : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hDiffScratch0 : Sg0 (EmitK.base (Kg.scratch .diffScratch)) = ([] : List Digit))
    (hQuery0 : Sg0 (EmitK.base (Kg.scratch .query)) = ([] : List Digit))
    (hQueryTmp0 : Sg0 (EmitK.base (Kg.scratch .queryTmp)) = ([] : List Digit))
    (hLogTmp0 : Sg0 (EmitK.base (Kg.scratch .logTmp)) = ([] : List MemSym))
    (hSumScratch0 : Sg0 (EmitK.base (Kg.scratch .sumScratch)) = ([] : List Digit))
    (hPrologueCounter0 : Sg0 (EmitK.base (Kg.scratch .prologueCounter)) = ([] : List Digit))
    (hPrologueWork0 : Sg0 (EmitK.base (Kg.scratch .prologueWork)) = ([] : List Digit))
    (hIo0 : Sg0 (EmitK.base Kg.io) = ([] : List Bool))
    (hBit : ∀ i < n, lookupD log (addr + i) 0 = 0 ∨ lookupD log (addr + i) 0 = 1) :
    ∃ n' sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n']
        (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
      = some ⟨none, sf, Sgf⟩
      ∧ Sgf EmitK.out = (OutputSlice.physicalBits log ⟨addr, n⟩).reverse := by
  have hScr0 : ∀ sk : ScratchKind, Sg0 (EmitK.base (Kg.scratch sk)) = [] := by
    intro sk
    cases sk
    exacts [hCopyScratch0, hQuery0, hQueryTmp0, hLogTmp0, hWorkRev0, hLhsOperand0, hRhsOperand0,
      hSumScratch0, hDiffScratch0, hPrologueCounter0, hPrologueWork0]
  obtain ⟨n12, sf2, Sg2, hrun12, hOut2, hReg2, hMem2, hScr2, hIo2, hCdf2, hn12⟩ :=
    master_run_bound_to_emit_done hSup oReg rAddr rDest rOne rLen hLO hAL hDL hDD hOA hOD n addr
      log regs0 sf0 Sg0 hsf0 hLen hAddr hOne hDest0 hRegs0 hMem0 hCd0 hOut0 hScr0 hIo0 hBit
  obtain ⟨n3, sf5, Sgf, hrun5, hOutF⟩ :=
    master_cleanup_run hSup oReg rAddr rDest rOne rLen
      (masterRunBoundRegs rAddr rDest rLen addr n regs0) (encodeLog log) [] [] [] [] [] [] [] []
      [] [] [] [] [] (MasterState.setCleanup sf2 ⟨false⟩) Sg2 hReg2 hMem2 (hScr2 .copyScratch)
      (hScr2 .query) (hScr2 .queryTmp) (hScr2 .logTmp) (hScr2 .workRev) (hScr2 .lhsOperand)
      (hScr2 .rhsOperand) (hScr2 .sumScratch) (hScr2 .diffScratch) (hScr2 .prologueCounter)
      (hScr2 .prologueWork) hIo2 hCdf2
  have hStep4 := master_flipBind_emit_done hSup oReg rAddr rDest rOne rLen sf2 Sg2
  have hC : (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n12 + 1]
      (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
    = some ⟨some (MasterΛ.cleanup (EmitCleanupPhase.drainReg ⟨0, by omega⟩)),
        MasterState.setCleanup sf2 ⟨false⟩, Sg2⟩ := by
    rw [Function.iterate_succ_apply', hrun12]; exact hStep4
  have hD : (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n3 + (n12 + 1)]
      (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
    = some ⟨none, sf5, Sgf⟩ := by
    rw [Function.iterate_add_apply, hC, hrun5]
  refine ⟨n3 + (n12 + 1), sf5, Sgf, hD, ?_⟩
  rw [hOutF, hOut2]

/-- Quantitative companion to `master_run_to_halt`: same statement, plus a bound on the witness
    step count. It stays at the same ABI-witness level as `master_run_to_halt` itself (register/
    scratch/mem/out/countdown values as explicit hypotheses, not derived from RAM semantics —
    that connection is supplied by the caller); adds a
    uniform register-content-length cap `M` for `master_cleanup_run_bound`'s sake, phrased
    against `regs0`/`addr+n` (the *inputs*) rather than the internal `regs` this proof builds,
    since the latter isn't available in the statement itself. -/
lemma master_run_bound (hLO : rOne ≠ rLen) (hAL : rAddr ≠ rLen) (hDL : rDest ≠ rLen)
    (hDD : rDest ≠ rAddr) (hOA : rOne ≠ rAddr) (hOD : rOne ≠ rDest)
    (n addr : ℕ) (log : WriteLog) (regs0 : Fin (regBound p) → ℕ) (M : ℕ)
    (hM0 : ∀ i : Fin (regBound p), (natToDigits (regs0 i)).length ≤ M)
    (hMaddr : (natToDigits (addr + n)).length ≤ M)
    (sf0 : MasterState p) (Sg0 : ∀ k, List (EmitΓ p k)) (hsf0 : sf0.prep = PrepState.canonical)
    (hLen : Sg0 (EmitK.base (Kg.reg rLen)) = natToDigits n)
    (hAddr : Sg0 (EmitK.base (Kg.reg rAddr)) = natToDigits addr)
    (hOne : Sg0 (EmitK.base (Kg.reg rOne)) = natToDigits 1)
    (hDest0 : Sg0 (EmitK.base (Kg.reg rDest)) = ([] : List Digit))
    (hRegs0 : ∀ i : Fin (regBound p), i ≠ rLen → i ≠ rAddr → i ≠ rDest →
      Sg0 (EmitK.base (Kg.reg i)) = natToDigits (regs0 i))
    (hMem0 : Sg0 (EmitK.base Kg.mem) = encodeLog log)
    (hCd0 : Sg0 EmitK.countdown = ([] : List Unit)) (hOut0 : Sg0 EmitK.out = [])
    (hWorkRev0 : Sg0 (EmitK.base (Kg.scratch .workRev)) = ([] : List Digit))
    (hCopyScratch0 : Sg0 (EmitK.base (Kg.scratch .copyScratch)) = ([] : List Digit))
    (hLhsOperand0 : Sg0 (EmitK.base (Kg.scratch .lhsOperand)) = ([] : List Digit))
    (hRhsOperand0 : Sg0 (EmitK.base (Kg.scratch .rhsOperand)) = ([] : List Digit))
    (hDiffScratch0 : Sg0 (EmitK.base (Kg.scratch .diffScratch)) = ([] : List Digit))
    (hQuery0 : Sg0 (EmitK.base (Kg.scratch .query)) = ([] : List Digit))
    (hQueryTmp0 : Sg0 (EmitK.base (Kg.scratch .queryTmp)) = ([] : List Digit))
    (hLogTmp0 : Sg0 (EmitK.base (Kg.scratch .logTmp)) = ([] : List MemSym))
    (hSumScratch0 : Sg0 (EmitK.base (Kg.scratch .sumScratch)) = ([] : List Digit))
    (hPrologueCounter0 : Sg0 (EmitK.base (Kg.scratch .prologueCounter)) = ([] : List Digit))
    (hPrologueWork0 : Sg0 (EmitK.base (Kg.scratch .prologueWork)) = ([] : List Digit))
    (hIo0 : Sg0 (EmitK.base Kg.io) = ([] : List Bool))
    (hBit : ∀ i < n, lookupD log (addr + i) 0 = 0 ∨ lookupD log (addr + i) 0 = 1) :
    ∃ n' sf Sgf, (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n']
        (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
        = some ⟨none, sf, Sgf⟩
        ∧ sf = MasterState.canonical
        ∧ Sgf EmitK.out = (OutputSlice.physicalBits log ⟨addr, n⟩).reverse
       ∧ (∀ i : Fin (regBound p), Sgf (EmitK.base (Kg.reg i)) = [])
       ∧ Sgf (EmitK.base Kg.mem) = []
       ∧ (∀ sk : ScratchKind, Sgf (EmitK.base (Kg.scratch sk)) = [])
       ∧ Sgf (EmitK.base Kg.io) = []
       ∧ Sgf EmitK.countdown = []
       ∧ n' ≤ (n * (16 * (2 * (natToDigits n).length + (natToDigits 1).length + 1) + 2) + 1) +
          (n * (32 * ((encodeLog log).length + (natToDigits (addr + n)).length + 1) ^ 2
              + 16 * (2 * (natToDigits (addr + n)).length + (natToDigits 1).length
                  + bitLen (addr + n) + bitLen 1 + 1)
              + 6) + 1) +
          ((0 + 1) + ((0 + 1) + ((0 + 1 + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) +
                (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1) + (0 + 1)) +
              (((encodeLog log).length + 1) + (regBound p * (M + 1) + 1)))) + 1) + 2 := by
  have hScr0 : ∀ sk : ScratchKind, Sg0 (EmitK.base (Kg.scratch sk)) = [] := by
    intro sk
    cases sk
    exacts [hCopyScratch0, hQuery0, hQueryTmp0, hLogTmp0, hWorkRev0, hLhsOperand0, hRhsOperand0,
      hSumScratch0, hDiffScratch0, hPrologueCounter0, hPrologueWork0]
  obtain ⟨n12, sf2, Sg2, hrun12, hOut2, hReg2, hMem2, hScr2, hIo2, hCdf2, hn12⟩ :=
    master_run_bound_to_emit_done hSup oReg rAddr rDest rOne rLen hLO hAL hDL hDD hOA hOD n addr
      log regs0 sf0 Sg0 hsf0 hLen hAddr hOne hDest0 hRegs0 hMem0 hCd0 hOut0 hScr0 hIo0 hBit
  have hStep4 := master_flipBind_emit_done hSup oReg rAddr rDest rOne rLen sf2 Sg2
  obtain ⟨n3, sf5, Sgf, hrun5, hsf5, hRegF, hMemF, hScrF, hIoF, hCdF, hOutF, hn3bound⟩ :=
    master_cleanup_run_bound hSup oReg rAddr rDest rOne rLen
      (masterRunBoundRegs rAddr rDest rLen addr n regs0) M
      (masterRunBoundRegs_length_le rAddr rDest rLen addr n regs0 M hM0 hMaddr) (encodeLog log)
      [] [] [] [] [] [] [] [] [] [] [] [] []
      (MasterState.setCleanup sf2 ⟨false⟩) Sg2 hReg2 hMem2 (hScr2 .copyScratch) (hScr2 .query)
      (hScr2 .queryTmp) (hScr2 .logTmp) (hScr2 .workRev) (hScr2 .lhsOperand) (hScr2 .rhsOperand)
      (hScr2 .sumScratch) (hScr2 .diffScratch) (hScr2 .prologueCounter) (hScr2 .prologueWork)
      hIo2 hCdf2
  simp only [List.length_nil] at hn3bound
  have hC : (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n12 + 1]
      (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
    = some ⟨some (MasterΛ.cleanup (EmitCleanupPhase.drainReg ⟨0, by omega⟩)),
        MasterState.setCleanup sf2 ⟨false⟩, Sg2⟩ := by
    rw [Function.iterate_succ_apply', hrun12]; exact hStep4
  have hD : (master_flipBind hSup oReg rAddr rDest rOne rLen)^[n3 + (n12 + 1)]
      (some ⟨some (MasterΛ.prep EmitPrepPhase.checkLen), sf0, Sg0⟩)
    = some ⟨none, sf5, Sgf⟩ := by
    rw [Function.iterate_add_apply, hC, hrun5]
  refine ⟨n3 + (n12 + 1), sf5, Sgf, hD, hsf5, ?_, hRegF, hMemF, hScrF, hIoF, hCdF, by omega⟩
  rw [hOutF, hOut2]

end NPComplete.RAMToTM.Generic
