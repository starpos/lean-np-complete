module

public import NPComplete.CookLevin.Recode.DecRun

/-!
# List Decoder Foundations

Block-based list decoding and raw preprocessing need shared facts about fixed-width encodings and
partial final blocks. This module keeps those representation facts and the finite-support machine
interfaces separate from execution proofs, so the decoder layers can reuse the same block model.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_succ stepsTo_trans)

variable (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)

noncomputable def decListReadTape (k : ℕ) (remaining : List Bool)
    (L R : List (Option Bool)) : Tape (Option Bool) :=
  match remaining with
  | [] => Tape.mk' (ListBlank.mk L)
      (ListBlank.mk (List.replicate k none ++ R))
  | b :: rest =>
      Tape.mk' (ListBlank.mk (rest.map some ++ L))
        (ListBlank.mk (some b :: List.replicate k none ++ R))

noncomputable def decListForwardTape (remaining : List Bool)
    (L : List (Option Bool)) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk L) (ListBlank.mk (tapeSymbols remaining))

lemma decListForwardTape_move_right (b : Bool) (rest : List Bool)
    (L : List (Option Bool)) :
    (decListForwardTape (b :: rest) L).move Dir.right =
      decListForwardTape rest (some b :: L) := by
  simp [decListForwardTape, Tape.move_right_mk', ListBlank.cons_mk,
    tapeSymbols]

lemma decListReadTape_nonempty_head (k : ℕ) (b : Bool) (rest : List Bool)
    (L R : List (Option Bool)) :
    (decListReadTape k (b :: rest) L R).head = some b := by
  simp [decListReadTape, Tape.mk']

lemma decListReadTape_mid_step (k : ℕ) (b c : Bool) (rest : List Bool)
    (L R : List (Option Bool)) :
    ((decListReadTape k (b :: c :: rest) L R).write none).move Dir.left =
      decListReadTape (k + 1) (c :: rest) L R := by
  simp [decListReadTape, Tape.write_mk', Tape.move_left_mk',
    ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk,
    List.replicate_succ]

lemma decListReadTape_last_step (k : ℕ) (b : Bool)
    (L R : List (Option Bool)) :
    (decListReadTape k [b] L R).write none =
      decListReadTape (k + 1) [] L R := by
  simp [decListReadTape, Tape.write_mk', ListBlank.tail_mk,
    ListBlank.cons_mk, List.replicate_succ]

@[reducible] noncomputable def decListN : ℕ :=
  (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n

inductive DecListPhase (n : ℕ)
  | seekFirst
  | seekEnd (hasOutput : Bool)
  | readBack (hasOutput : Bool) (i : Fin n.succ)
      (acc : List.Vector Bool i.val)
  | readBackMove (hasOutput : Bool) (i : Fin n.succ)
      (acc : List.Vector Bool i.val)
  | readBackFinish (b : Bool)
  | partialRestart (hasOutput : Bool)
  | seekSep (b : Bool)
  | seekOut (b : Bool)
  | checkOutput
  | checkInput
  | findOut
  | walkOutLeft
  | done
  deriving DecidableEq

instance {n : ℕ} : Inhabited (DecListPhase n) :=
  ⟨DecListPhase.seekFirst⟩

def decListFinNext {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then
    ⟨i.val + 1, h⟩
  else
    ⟨0, hn⟩

def decListFinPred {n : ℕ} (i : Fin n) (hi : 0 < i.val) : Fin n :=
  ⟨i.val - 1, by omega⟩

inductive RawDecListPhase (n : ℕ)
  | seekFirst
  | scanRight (i : Fin n)
  | trimRight (i : Fin n)
  | trimErase (i : Fin n)
  | rewindStart
  | rewindLeft
  | run (q : DecListPhase n)
  deriving DecidableEq

instance {n : ℕ} : Inhabited (RawDecListPhase n) :=
  ⟨RawDecListPhase.seekFirst⟩

noncomputable def decListResult (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (bits : List.Vector Bool (decListN tm)) : Bool :=
  match ((BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).dec bits).2 tm.k₁ with
  | some x => out x.1
  | none => false

noncomputable def decListCell (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (c : TM2to1.Γ' tm.K (TM2to1.PackΓ tm)) : Bool :=
  match c.2 tm.k₁ with
  | some x => out x.1
  | none => false

noncomputable def decodePackedOutputList (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (l : List Bool) : List Bool :=
  let eΓ := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  (eΓ.decodeList l).map (decListCell tm out)

noncomputable def decListMachine (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0.Machine (Option Bool) (DecListPhase (decListN tm)) :=
  let eΓ := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  fun phase cell =>
    match phase with
    | DecListPhase.seekFirst =>
        match cell with
        | some b => some (.checkInput, TM0.Stmt.write (some b))
        | none => some (.done, TM0.Stmt.write none)
    | DecListPhase.seekEnd hasOutput =>
        match cell with
        | some _ => some (.seekEnd hasOutput, TM0.Stmt.move Dir.right)
        | none =>
            if h : 0 < eΓ.n then
              some (.readBack hasOutput ⟨0, by omega⟩ .nil,
                TM0.Stmt.move Dir.left)
            else
              some (.done, TM0.Stmt.write none)
    | DecListPhase.readBack hasOutput i acc =>
        match cell with
        | none => some (.partialRestart hasOutput, TM0.Stmt.move Dir.left)
        | some b =>
            if h : i.val + 1 < eΓ.n then
              some (.readBackMove hasOutput ⟨i.val + 1, by
                change i.val + 1 < eΓ.n + 1
                omega⟩ (acc.cons b), TM0.Stmt.write none)
            else if h : i.val + 1 = eΓ.n then
              let bits : List.Vector Bool eΓ.n :=
                ⟨(acc.cons b).toList, by
                  simp [List.Vector.toList_length, h]⟩
              some (.readBackFinish (decListResult tm out bits), TM0.Stmt.write none)
            else
              some (.partialRestart hasOutput, TM0.Stmt.move Dir.left)
    | DecListPhase.readBackMove hasOutput i acc =>
        some (.readBack hasOutput i acc, TM0.Stmt.move Dir.left)
    | DecListPhase.readBackFinish b =>
        some (.seekSep b, TM0.Stmt.move Dir.left)
    | DecListPhase.partialRestart hasOutput =>
        match cell with
        | some b => some (.seekEnd hasOutput, TM0.Stmt.write (some b))
        | none => some (.checkInput, TM0.Stmt.write none)
    | DecListPhase.seekSep b =>
        match cell with
        | some _ => some (.seekSep b, TM0.Stmt.move Dir.left)
        | none => some (.seekOut b, TM0.Stmt.move Dir.left)
    | DecListPhase.seekOut b =>
        match cell with
        | some _ => some (.seekOut b, TM0.Stmt.move Dir.left)
        | none => some (.checkOutput, TM0.Stmt.write (some b))
    | DecListPhase.checkOutput =>
        match cell with
        | some _ => some (.checkOutput, TM0.Stmt.move Dir.right)
        | none => some (.checkInput, TM0.Stmt.move Dir.right)
    | DecListPhase.checkInput =>
        match cell with
        | some b => some (.seekEnd true, TM0.Stmt.write (some b))
        | none => some (.findOut, TM0.Stmt.move Dir.left)
    | DecListPhase.findOut =>
        match cell with
        | some _ => some (.walkOutLeft, TM0.Stmt.move Dir.left)
        | none => some (.walkOutLeft, TM0.Stmt.move Dir.left)
    | DecListPhase.walkOutLeft =>
        match cell with
        | some _ => some (.walkOutLeft, TM0.Stmt.move Dir.left)
        | none => some (.done, TM0.Stmt.move Dir.right)
    | DecListPhase.done => none

noncomputable def decListRawMachine (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0.Machine (Option Bool) (RawDecListPhase (decListN tm)) :=
  let eΓ := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  let hn : 0 < eΓ.n := by
    simpa [decListN, decN] using decN_pos tm
  fun phase cell =>
    match phase with
    | RawDecListPhase.seekFirst =>
        match cell with
        | some b =>
            some (.scanRight (decListFinNext hn ⟨0, hn⟩),
              TM0.Stmt.move Dir.right)
        | none => some (.run .done, TM0.Stmt.write none)
    | RawDecListPhase.scanRight i =>
        match cell with
        | some _ =>
            some (.scanRight (decListFinNext hn i), TM0.Stmt.move Dir.right)
        | none => some (.trimRight i, TM0.Stmt.write none)
    | RawDecListPhase.trimRight i =>
        if hi : i.val = 0 then
          some (.rewindStart, TM0.Stmt.write none)
        else
          some (.trimErase i, TM0.Stmt.move Dir.left)
    | RawDecListPhase.trimErase i =>
        if hzero : i.val = 0 then
          some (.rewindStart, TM0.Stmt.write none)
        else if hi : i.val = 1 then
          some (.rewindStart, TM0.Stmt.write none)
        else
          some (.trimRight (decListFinPred i (by omega)), TM0.Stmt.write none)
    | RawDecListPhase.rewindStart =>
        some (.rewindLeft, TM0.Stmt.move Dir.left)
    | RawDecListPhase.rewindLeft =>
        match cell with
        | some _ => some (.rewindLeft, TM0.Stmt.move Dir.left)
        | none => some (.run (.seekEnd false), TM0.Stmt.move Dir.right)
    | RawDecListPhase.run q =>
        match decListMachine tm out q cell with
        | none => none
        | some (q', s) => some (.run q', s)

noncomputable def decListElems (n : ℕ) : List (DecListPhase n) :=
  [DecListPhase.seekEnd false, DecListPhase.seekEnd true,
    DecListPhase.seekSep false, DecListPhase.seekSep true,
    DecListPhase.seekOut false, DecListPhase.seekOut true,
    DecListPhase.checkOutput, DecListPhase.checkInput,
    DecListPhase.partialRestart false, DecListPhase.partialRestart true,
    DecListPhase.seekFirst, DecListPhase.findOut, DecListPhase.walkOutLeft,
    DecListPhase.done] ++
    [false, true].flatMap (fun hasOutput =>
      (List.finRange n.succ).flatMap fun i =>
        (Finset.univ : Finset (List.Vector Bool i.val)).toList.map
          (fun acc => DecListPhase.readBack hasOutput i acc)) ++
    [false, true].flatMap (fun hasOutput =>
      (List.finRange n.succ).flatMap fun i =>
        (Finset.univ : Finset (List.Vector Bool i.val)).toList.map
          (fun acc => DecListPhase.readBackMove hasOutput i acc)) ++
    [false, true].map DecListPhase.readBackFinish

noncomputable def decListSupport (n : ℕ) : Finset (DecListPhase n) :=
  (decListElems n).toFinset

noncomputable def decListRawElems (n : ℕ) : List (RawDecListPhase n) :=
  [RawDecListPhase.seekFirst] ++
    (List.finRange n).map RawDecListPhase.scanRight ++
    (List.finRange n).map RawDecListPhase.trimRight ++
    (List.finRange n).map RawDecListPhase.trimErase ++
    [RawDecListPhase.rewindStart, RawDecListPhase.rewindLeft] ++
    (decListElems n).map RawDecListPhase.run

noncomputable def decListRawSupport (n : ℕ) : Finset (RawDecListPhase n) :=
  (decListRawElems n).toFinset

lemma mem_decListRawSupport_seekFirst (n : ℕ) :
    RawDecListPhase.seekFirst ∈ decListRawSupport n := by
  simp [decListRawSupport, decListRawElems]

lemma mem_decListRawSupport_scanRight (n : ℕ) (i : Fin n) :
    RawDecListPhase.scanRight i ∈ decListRawSupport n := by
  simp [decListRawSupport, decListRawElems]

lemma mem_decListRawSupport_trimRight (n : ℕ) (i : Fin n) :
    RawDecListPhase.trimRight i ∈ decListRawSupport n := by
  simp [decListRawSupport, decListRawElems]

lemma mem_decListRawSupport_trimErase (n : ℕ) (i : Fin n) :
    RawDecListPhase.trimErase i ∈ decListRawSupport n := by
  simp [decListRawSupport, decListRawElems]

lemma mem_decListRawSupport_rewindStart (n : ℕ) :
    RawDecListPhase.rewindStart ∈ decListRawSupport n := by
  simp [decListRawSupport, decListRawElems]

lemma mem_decListRawSupport_rewindLeft (n : ℕ) :
    RawDecListPhase.rewindLeft ∈ decListRawSupport n := by
  simp [decListRawSupport, decListRawElems]

lemma mem_decListRawSupport_run (n : ℕ) (q : DecListPhase n)
    (hq : q ∈ decListSupport n) :
    RawDecListPhase.run q ∈ decListRawSupport n := by
  simp [decListRawSupport, decListRawElems, decListSupport] at hq ⊢
  exact hq

lemma mem_decListSupport_seekEnd (n : ℕ) (h : Bool) :
    DecListPhase.seekEnd h ∈ decListSupport n := by
  cases h <;> simp [decListSupport, decListElems]

lemma mem_decListSupport_seekFirst (n : ℕ) :
    DecListPhase.seekFirst ∈ decListSupport n := by
  simp [decListSupport, decListElems]

lemma mem_decListSupport_seekSep (n : ℕ) (b : Bool) :
    DecListPhase.seekSep b ∈ decListSupport n := by
  cases b <;> simp [decListSupport, decListElems]

lemma mem_decListSupport_seekOut (n : ℕ) (b : Bool) :
    DecListPhase.seekOut b ∈ decListSupport n := by
  cases b <;> simp [decListSupport, decListElems]

lemma mem_decListSupport_fixed (n : ℕ) :
    DecListPhase.checkOutput ∈ decListSupport n ∧
      DecListPhase.checkInput ∈ decListSupport n ∧
      DecListPhase.findOut ∈ decListSupport n ∧
      DecListPhase.walkOutLeft ∈ decListSupport n ∧
      DecListPhase.done ∈ decListSupport n := by
  simp [decListSupport, decListElems]

lemma mem_decListSupport_readBack (n : ℕ) (h : Bool)
    (i : Fin n.succ) (acc : List.Vector Bool i.val) :
    DecListPhase.readBack h i acc ∈ decListSupport n := by
  simp [decListSupport, decListElems, List.mem_finRange]

lemma mem_decListSupport_readBackMove (n : ℕ) (h : Bool)
    (i : Fin n.succ) (acc : List.Vector Bool i.val) :
    DecListPhase.readBackMove h i acc ∈ decListSupport n := by
  simp [decListSupport, decListElems, List.mem_finRange]

lemma mem_decListSupport_readBackFinish (n : ℕ) (b : Bool) :
    DecListPhase.readBackFinish b ∈ decListSupport n := by
  cases b <;> simp [decListSupport, decListElems]

lemma mem_decListSupport_partialRestart (n : ℕ) (h : Bool) :
    DecListPhase.partialRestart h ∈ decListSupport n := by
  cases h <;> simp [decListSupport, decListElems]

lemma decListMachine_supports (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0.Supports (decListMachine tm out) (↑(decListSupport (decListN tm))) := by
  refine ⟨?_, ?_⟩
  · simpa [default] using mem_decListSupport_seekFirst (decListN tm)
  · intro q a q' s hstep hq
    revert q' s hstep
    cases q <;> intro q' s hstep <;>
      simp [decListMachine] at hstep <;>
      (try cases a) <;> (try split_ifs at hstep) <;>
      (try rcases hstep with ⟨rfl, rfl⟩) <;>
      first
      | exact mem_decListSupport_seekEnd _ _
      | exact mem_decListSupport_seekSep _ _
      | exact mem_decListSupport_seekOut _ _
      | exact (mem_decListSupport_fixed _).1
      | exact (mem_decListSupport_fixed _).2.1
      | exact (mem_decListSupport_fixed _).2.2.1
      | exact (mem_decListSupport_fixed _).2.2.2.1
      | exact (mem_decListSupport_fixed _).2.2.2.2
      | exact mem_decListSupport_readBack _ _ _ _
      | exact mem_decListSupport_readBackMove _ _ _ _
      | exact mem_decListSupport_readBackFinish _ _
      | exact mem_decListSupport_partialRestart _ _

lemma decListRawMachine_supports (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0.Supports (decListRawMachine tm out)
      (↑(decListRawSupport (decListN tm))) := by
  refine ⟨?_, ?_⟩
  · simpa [default] using mem_decListRawSupport_seekFirst (decListN tm)
  · intro q a q' s hstep hq
    revert q' s hstep
    cases q with
    | seekFirst =>
        intro q' s hstep
        cases a with
        | none =>
            simp [decListRawMachine] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact mem_decListRawSupport_run _ _
              (mem_decListSupport_fixed _).2.2.2.2
        | some b =>
            simp [decListRawMachine] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact mem_decListRawSupport_scanRight _ _
    | scanRight i =>
        intro q' s hstep
        cases a with
        | none =>
            simp [decListRawMachine] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact mem_decListRawSupport_trimRight _ _
        | some b =>
            simp [decListRawMachine] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact mem_decListRawSupport_scanRight _ _
    | trimRight i =>
        intro q' s hstep
        simp [decListRawMachine] at hstep
        split_ifs at hstep
        · rcases hstep with ⟨rfl, rfl⟩
          exact mem_decListRawSupport_rewindStart _
        · rcases hstep with ⟨rfl, rfl⟩
          exact mem_decListRawSupport_trimErase _ _
    | trimErase i =>
        intro q' s hstep
        simp [decListRawMachine] at hstep
        split_ifs at hstep
        · rcases hstep with ⟨rfl, rfl⟩
          exact mem_decListRawSupport_rewindStart _
        · rcases hstep with ⟨rfl, rfl⟩
          exact mem_decListRawSupport_rewindStart _
        · rcases hstep with ⟨rfl, rfl⟩
          exact mem_decListRawSupport_trimRight _ _
    | rewindStart =>
        intro q' s hstep
        simp [decListRawMachine] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        exact mem_decListRawSupport_rewindLeft _
    | rewindLeft =>
        intro q' s hstep
        cases a with
        | none =>
            simp [decListRawMachine] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact mem_decListRawSupport_run _ _
              (mem_decListSupport_seekEnd _ false)
        | some b =>
            simp [decListRawMachine] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            exact mem_decListRawSupport_rewindLeft _
    | run q =>
        intro q' s hstep
        have hq' : q ∈ decListSupport (decListN tm) := by
          simpa [decListRawSupport, decListRawElems, decListSupport] using hq
        simp [decListRawMachine] at hstep
        cases h : decListMachine tm out q a with
        | none => simp [h] at hstep
        | some p =>
            rcases p with ⟨q₂, s₂⟩
            simp [h] at hstep
            rcases hstep with ⟨rfl, rfl⟩
            have hpair : (q₂, s₂) ∈ decListMachine tm out q a := by
              rw [h]
              simp
            have hq₂ := (decListMachine_supports tm out).2 hpair hq'
            exact mem_decListRawSupport_run _ _ hq₂


end NPComplete.CookLevin
