module

public import NPComplete.CookLevin.Recode
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.Encoding

/-!
To recover a Boolean output from a packed finite-alphabet computation, the
recoding needs a finite-state decoder on the Boolean tape. This module defines
that decoder and proves its state transitions, its local execution facts, and an
arithmetic bound for `recodeTime`; the run-level behavior is proved in `DecRun.lean`.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_trans)

inductive DecPhase (n : ℕ)
  | read (i : Fin n.succ) (acc : List.Vector Bool i.val)
  | goHome (left : Fin n.succ) (b : Bool)
  | writeOut (b : Bool)
  | skipBit
  | eraseRest
  | eraseRestGo
  | backToBit
  | done
  deriving DecidableEq

instance {n : ℕ} : Inhabited (DecPhase n) :=
  ⟨DecPhase.read ⟨0, Nat.succ_pos _⟩ .nil⟩

noncomputable def decMachine (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0.Machine (Option Bool) (DecPhase
      (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n) :=
  let eΓ := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  fun phase cell =>
    match phase with
    | DecPhase.read i acc =>
        let b := Option.getD cell false
        if h : i.val + 1 < eΓ.n.succ then
          if heq : i.val + 1 = eΓ.n then
            let acc' := acc.cons b
            let bits : List.Vector Bool eΓ.n :=
              ⟨acc'.toList.reverse, by
                simp [List.length_reverse, List.Vector.toList_length, heq]⟩
            let result : Bool :=
              match (eΓ.dec bits).2 tm.k₁ with
              | some x => out x.1
              | none => false
            some (DecPhase.goHome ⟨eΓ.n, Nat.lt_succ_self _⟩ result,
              TM0.Stmt.move Dir.right)
          else
            some (DecPhase.read ⟨i.val + 1, h⟩ (acc.cons b), TM0.Stmt.move Dir.right)
        else
          some (DecPhase.writeOut false, TM0.Stmt.write (some false))
    | DecPhase.goHome left b =>
        if h : 0 < left.val then
          some (DecPhase.goHome ⟨left.val - 1, by omega⟩ b, TM0.Stmt.move Dir.left)
        else
          some (DecPhase.writeOut b, TM0.Stmt.write (some b))
    | DecPhase.writeOut b =>
        some (DecPhase.skipBit, TM0.Stmt.write (some b))
    | DecPhase.skipBit =>
        some (DecPhase.eraseRest, TM0.Stmt.move Dir.right)
    | DecPhase.eraseRest =>
        match cell with
        | some _ => some (DecPhase.eraseRestGo, TM0.Stmt.write none)
        | none => some (DecPhase.backToBit, TM0.Stmt.move Dir.left)
    | DecPhase.eraseRestGo =>
        some (DecPhase.eraseRest, TM0.Stmt.move Dir.right)
    | DecPhase.backToBit =>
        match cell with
        | none => some (DecPhase.backToBit, TM0.Stmt.move Dir.left)
        | some _ => some (DecPhase.done, TM0.Stmt.write cell)
    | DecPhase.done => none

noncomputable def decElems (n : ℕ) : List (DecPhase n) :=
  [DecPhase.done, DecPhase.skipBit, DecPhase.eraseRest, DecPhase.eraseRestGo,
    DecPhase.backToBit] ++
    [false, true].map DecPhase.writeOut ++
    [false, true].flatMap (fun b =>
      (List.finRange n.succ).map fun i => DecPhase.goHome i b) ++
    (List.finRange n.succ).flatMap fun i =>
      (Finset.univ : Finset (List.Vector Bool i.val)).toList.map
        fun acc => DecPhase.read i acc

noncomputable def decSupport (n : ℕ) : Finset (DecPhase n) :=
  decElems n |>.toFinset

lemma mem_decSupport_done (n : ℕ) : DecPhase.done ∈ decSupport n := by
  simp [decSupport, decElems]

lemma mem_decSupport_skipBit (n : ℕ) : DecPhase.skipBit ∈ decSupport n := by
  simp [decSupport, decElems]

lemma mem_decSupport_eraseRest (n : ℕ) : DecPhase.eraseRest ∈ decSupport n := by
  simp [decSupport, decElems]

lemma mem_decSupport_eraseRestGo (n : ℕ) : DecPhase.eraseRestGo ∈ decSupport n := by
  simp [decSupport, decElems]

lemma mem_decSupport_backToBit (n : ℕ) : DecPhase.backToBit ∈ decSupport n := by
  simp [decSupport, decElems]

lemma mem_decSupport_goHome (n : ℕ) (i : Fin n.succ) (b : Bool) :
    DecPhase.goHome i b ∈ decSupport n := by
  cases b <;> simp [decSupport, decElems, List.mem_finRange]

lemma mem_decSupport_writeOut (n : ℕ) (b : Bool) :
    DecPhase.writeOut b ∈ decSupport n := by
  cases b <;> simp [decSupport, decElems]

lemma mem_decSupport_read (n : ℕ) (i : Fin n.succ)
    (acc : List.Vector Bool i.val) :
    DecPhase.read i acc ∈ decSupport n := by
  simp [decSupport, decElems, List.mem_finRange]

lemma decMachine_supports (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0.Supports (decMachine tm out)
      ↑(decSupport (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n) := by
  refine ⟨?_, ?_⟩
  · simpa [default] using
      mem_decSupport_read
        (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n
        ⟨0, Nat.succ_pos _⟩ .nil
  · intro q a q' s hstep hq
    revert q' s hstep
    cases q <;> intro q' s hstep <;>
      simp [decMachine] at hstep <;>
      (try cases a) <;> (try split_ifs at hstep) <;>
      (try rcases hstep with ⟨rfl, rfl⟩) <;>
      first
      | exact mem_decSupport_done _
      | exact mem_decSupport_skipBit _
      | exact mem_decSupport_eraseRest _
      | exact mem_decSupport_eraseRestGo _
      | exact mem_decSupport_backToBit _
      | exact mem_decSupport_writeOut _ _
      | exact mem_decSupport_goHome _ _ _
      | exact mem_decSupport_read _ _ _

noncomputable def decAux (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0ComputableAux Bool where
  Λ := DecPhase (BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))).n
  M := decMachine tm out
  S := decSupport _
  supports := decMachine_supports tm out

noncomputable def decodePackedOutputBool (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (l : List Bool) : Bool :=
  match decodePackedOutput tm out l with
  | b :: _ => b
  | [] => false

lemma decMachine_done_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (cell : Option Bool) :
    decMachine tm out .done cell = none :=
  rfl

lemma decMachine_writeOut (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (cell : Option Bool) :
    decMachine tm out (.writeOut b) cell =
      some (.skipBit, TM0.Stmt.write (some b)) :=
  rfl

lemma dec_writeOut_step (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (T : Tape (Option Bool)) :
    TM0.step (decMachine tm out) ⟨.writeOut b, T⟩ =
      some ⟨.skipBit, T.write (some b)⟩ := by
  simp [TM0.step, decMachine_writeOut]

lemma dec_done_halt (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) :
    TM0.step (decMachine tm out) ⟨.done, T⟩ = none := by
  simp [step_eq_none_iff, decMachine_done_none]

lemma tape_mk₁_write_bit (b : Bool) :
    Tape.write (some b) (Tape.mk₁ (tapeSymbols ([] : List Bool))) =
      Tape.mk₁ (tapeSymbols [b]) := by
  simp [tapeSymbols, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.write,
    ListBlank.head_mk, ListBlank.tail_mk]

lemma dec_skipBit_step (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) :
    TM0.step (decMachine tm out) ⟨.skipBit, T⟩ =
      some ⟨.eraseRest, T.move Dir.right⟩ := by
  simp [TM0.step, decMachine]

lemma dec_eraseRest_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step (decMachine tm out) ⟨.eraseRest, T⟩ =
      some ⟨.backToBit, T.move Dir.left⟩ := by
  simp [TM0.step, decMachine, h]

lemma dec_eraseRest_some (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) {x : Bool} (h : T.head = some x) :
    TM0.step (decMachine tm out) ⟨.eraseRest, T⟩ =
      some ⟨.eraseRestGo, T.write none⟩ := by
  simp [TM0.step, decMachine, h]

lemma dec_eraseRestGo_step (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) :
    TM0.step (decMachine tm out) ⟨.eraseRestGo, T⟩ =
      some ⟨.eraseRest, T.move Dir.right⟩ := by
  simp [TM0.step, decMachine]

lemma dec_backToBit_some (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) (h : T.head ≠ none) :
    TM0.step (decMachine tm out) ⟨.backToBit, T⟩ =
      some ⟨.done, T.write T.head⟩ := by
  cases h' : T.head
  · exact (h h').elim
  · simp [TM0.step, decMachine, h']

lemma dec_backToBit_none (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool)
    (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step (decMachine tm out) ⟨.backToBit, T⟩ =
      some ⟨.backToBit, T.move Dir.left⟩ := by
  simp [TM0.step, decMachine, h]

lemma mk₁_bit_head (b : Bool) :
    (Tape.mk₁ (tapeSymbols [b])).head = some b := by
  simp [tapeSymbols, Tape.mk₁, Tape.mk₂, Tape.mk']

lemma mk₁_bit_write_self (b : Bool) :
    (Tape.mk₁ (tapeSymbols [b])).write (some b) =
      Tape.mk₁ (tapeSymbols [b]) := by
  simp [tapeSymbols, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.write, ListBlank.head_mk]

end NPComplete.CookLevin
