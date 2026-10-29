module

public import NPComplete.CookLevin.Recode.Sim.CleanMoves

/-!
# Normal-Step Preservation for Clean Simulation

Microstep proofs depend on tape-shape case splits, while the simulator needs one preservation result
for each source statement. This module combines the write and move cases into a uniform normal-state
step contract, so callers need not repeat endpoint analysis.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

def simCleanStmtTime {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (s : TM0.Stmt Γ) : ℕ :=
  match s with
  | .write _ => 6 * e.n + 4
  | .move _ => 4 * e.n + 4

/-! One source statement step at a fully nonempty interior position.  This is
    the first bridge from the two representative relations to the sum-valued
    state relation; endpoint cases use the blank wrappers above. -/

lemma simCleanMachine_normal_stmt_step_interior {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s : TM0.Stmt Γ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (l r : List Γ) (bl br : List (List (Option Bool)))
    (a : Γ) (b : List (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk l) (ListBlank.mk (a :: r)))
    (hU : U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk (b ++ rawBlocksRight br)))
    (hbl : RawBlocksRel e bl l) (hbr : RawBlocksRel e br r)
    (hb : BlockDecodes e b a) (hblm : BlocksMarked bl)
    (hl : ∃ x xs, l = x :: xs) (hr : ∃ y ys, r = y :: ys)
    (hm : M q T.head = some (q', s)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (simCleanStmtTime e s) ∧
      RawTapeCleanStateRel e
        (match s with
        | .write a => T.write a
        | .move d => T.move d) U' := by
  have hhead : T.head = a := by
    rw [hT]
    rfl
  have hm' : M q a = some (q', s) := by
    simpa [hhead] using hm
  have hold : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simp [hold]⟩ = a :=
    hb.choose_spec
  rcases hl with ⟨x, xs, rfl⟩
  rcases hr with ⟨y, ys, rfl⟩
  cases hbl with
  | @cons b₀ x bl' xs hb₀ hbl' =>
      cases hbr with
      | @cons b₂ y br' ys hb₂ hbr' =>
          have hb₀m : BlockMarked b₀ :=
            (blocksMarked_cons.mp hblm).1
          have hblm' : BlocksMarked bl' :=
            (blocksMarked_cons.mp hblm).2
          have hblfull : RawBlocksRel e (b₀ :: bl') (x :: xs) :=
            RawBlocksRel.cons hb₀ hbl'
          let L₀ : ListBlank (Option Bool) :=
            ListBlank.mk (rawBlocksLeft bl')
          have hL :
              ListBlank.mk (rawBlocksLeft (b₀ :: bl')) =
                ListBlank.append b₀.reverse L₀ := by
            simp [L₀, rawBlocksLeft_cons]
          cases s with
          | write z =>
              obtain ⟨bits, U', hbits, hsteps, hstate⟩ :=
                simCleanMachine_write_boundary_nonempty M e q q'
                  z a y (x :: xs) ys (b₀ :: bl') br' b₂ b
                  (ListBlank.mk (rawBlocksLeft (b₀ :: bl'))) T U
                  hT
                  (by simp [hU, rawBlocksRight_cons])
                  (by rfl) hblfull hbr' hblm hold hdec hb₂ hm' hn
              exact ⟨U', hsteps,
                RawTapeCleanStateRel.boundary hstate⟩
          | move d =>
              cases d with
              | right =>
                  obtain ⟨bits, U', hbits, hsteps, hstate⟩ :=
                    simCleanMachine_move_right_rawTapeCleanRel M e q q'
                      a y (x :: xs) ys (b₀ :: bl') br' b b₂
                      (ListBlank.mk (rawBlocksLeft (b₀ :: bl'))) T U
                      hT
                      (by simp [hU, rawBlocksRight_cons])
                      (by rfl) hblfull hbr' hblm hold hdec hb₂ hm' hn
                  exact ⟨U', hsteps,
                    RawTapeCleanStateRel.normal hstate⟩
              | left =>
                  obtain ⟨bits, U', hbits, hsteps, hstate⟩ :=
                    simCleanMachine_move_left_rawTapeCleanRel_nonempty M e
                      q q' a x y xs ys bl' br'
                      b₀ b₂ b L₀
                      (ListBlank.mk (rawBlocksLeft (b₀ :: bl'))) T U
                      hT
                      (by rfl) hL
                      (by simp [hU, rawBlocksRight_cons])
                      hbl' hbr' hb₀ hb₀m hblm' hold hdec hb₂ hm' hn
                  exact ⟨U', hsteps,
                    RawTapeCleanStateRel.normal hstate⟩

/-- The fully populated step, repackaged with the clean relation as postcondition. -/
lemma simCleanMachine_normal_stmt_step_interior_rawTapeCleanRel {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s : TM0.Stmt Γ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (l r : List Γ) (bl br : List (List (Option Bool)))
    (a : Γ) (b : List (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk l) (ListBlank.mk (a :: r)))
    (hU : U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk (b ++ rawBlocksRight br)))
    (hbl : RawBlocksRel e bl l) (hbr : RawBlocksRel e br r)
    (hb : BlockDecodes e b a) (hblm : BlocksMarked bl)
    (hl : ∃ x xs, l = x :: xs) (hr : ∃ y ys, r = y :: ys)
    (hm : M q T.head = some (q', s)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (simCleanStmtTime e s) ∧
      RawTapeCleanRel e
        (match s with
        | .write a => T.write a
        | .move d => T.move d) U' := by
  obtain ⟨U', hsteps, hstate⟩ :=
    simCleanMachine_normal_stmt_step_interior M e q q' s T U l r bl br a b
      hT hU hbl hbr hb hblm hl hr hm hn
  cases hstate with
  | normal hnormal => exact ⟨U', hsteps, hnormal⟩
  | boundary hboundary =>
      exact ⟨U', hsteps, rawTapeCleanBoundaryRel_to_rawTapeCleanRel hboundary⟩

/-- Write case of the normal source step, dispatching on neighbouring block existence. -/
lemma simCleanMachine_normal_stmt_step_write {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (z : Γ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (hrel : RawTapeCleanRel e T U)
    (hm : M q T.head = some (q', TM0.Stmt.write z)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.write z)) ∧
      RawTapeCleanRel e (T.write z) U' := by
  rcases hrel with ⟨l, r, bl, br, a, b, hT, hU, hbl, hbr, hb, hblm⟩
  have hm' : M q a = some (q', TM0.Stmt.write z) := by
    simpa [show T.head = a by rw [hT]; rfl] using hm
  have hblen : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simpa using hblen⟩ = a :=
    hb.choose_spec
  cases hbl with
  | nil =>
      cases hbr with
      | nil =>
          obtain ⟨_, U', _, hsteps, hrel'⟩ :=
            simCleanMachine_write_boundary_blank_general M e q q' z a
              [] [] b (ListBlank.mk []) T U hT
              (by simp [hU, rawBlocksLeft, rawBlocksRight]) rfl
              RawBlocksRel.nil blocksMarked_nil hblen hdec hm' hn
          exact ⟨U', hsteps, rawTapeCleanBoundaryRel_to_rawTapeCleanRel hrel'⟩
      | @cons b₂ y br' ys hb₂ hbr' =>
          obtain ⟨_, U', _, hsteps, hrel'⟩ :=
            simCleanMachine_write_boundary_nonempty M e q q' z a y
              [] ys [] br' b₂ b (ListBlank.mk []) T U hT
              (by simp [hU, rawBlocksLeft, rawBlocksRight]) rfl RawBlocksRel.nil
              hbr' blocksMarked_nil hblen hdec hb₂ hm' hn
          exact ⟨U', hsteps, rawTapeCleanBoundaryRel_to_rawTapeCleanRel hrel'⟩
  | @cons b₀ x bl' xs hb₀ hbl' =>
      cases hbr with
      | nil =>
          obtain ⟨_, U', _, hsteps, hrel'⟩ :=
            simCleanMachine_write_boundary_blank_general M e q q' z a
              (x :: xs) (b₀ :: bl') b
              (ListBlank.mk (rawBlocksLeft (b₀ :: bl'))) T U hT
              (by simp [hU, rawBlocksLeft, rawBlocksRight]) (by rfl)
              (RawBlocksRel.cons hb₀ hbl') hblm hblen hdec hm' hn
          exact ⟨U', hsteps, rawTapeCleanBoundaryRel_to_rawTapeCleanRel hrel'⟩
      | @cons b₂ y br' ys hb₂ hbr' =>
          exact simCleanMachine_normal_stmt_step_interior_rawTapeCleanRel M e q q'
            (.write z) T U (x :: xs) (y :: ys) (b₀ :: bl') (b₂ :: br') a b
            hT hU (RawBlocksRel.cons hb₀ hbl') (RawBlocksRel.cons hb₂ hbr')
            hb hblm ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩ hm hn

/-- Right-move case of the normal source step, dispatching on neighbouring block existence. -/
lemma simCleanMachine_normal_stmt_step_move_right {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (hrel : RawTapeCleanRel e T U)
    (hm : M q T.head = some (q', TM0.Stmt.move Dir.right)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.move Dir.right)) ∧
      RawTapeCleanRel e (T.move Dir.right) U' := by
  rcases hrel with ⟨l, r, bl, br, a, b, hT, hU, hbl, hbr, hb, hblm⟩
  have hm' : M q a = some (q', TM0.Stmt.move Dir.right) := by
    simpa [show T.head = a by rw [hT]; rfl] using hm
  have hblen : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simpa using hblen⟩ = a :=
    hb.choose_spec
  cases hbl with
  | nil =>
      cases hbr with
      | nil =>
          obtain ⟨_, U', _, hsteps, hrel'⟩ :=
            simCleanMachine_move_right_rawTapeCleanRel_blank M e q q' a
              [] [] b (ListBlank.mk []) T U hT
              (by simp [hU, rawBlocksLeft, rawBlocksRight]) rfl
              RawBlocksRel.nil blocksMarked_nil hblen hdec hm' hn
          exact ⟨U', hsteps, hrel'⟩
      | @cons b₂ y br' ys hb₂ hbr' =>
          obtain ⟨_, U', _, hsteps, hrel'⟩ :=
            simCleanMachine_move_right_rawTapeCleanRel M e q q' a y
              [] ys [] br' b b₂ (ListBlank.mk []) T U hT
              (by simp [hU, rawBlocksLeft, rawBlocksRight]) rfl RawBlocksRel.nil
              hbr' blocksMarked_nil hblen hdec hb₂ hm' hn
          exact ⟨U', hsteps, hrel'⟩
  | @cons b₀ x bl' xs hb₀ hbl' =>
      cases hbr with
      | nil =>
          obtain ⟨_, U', _, hsteps, hrel'⟩ :=
            simCleanMachine_move_right_rawTapeCleanRel_blank M e q q' a
              (x :: xs) (b₀ :: bl') b
              (ListBlank.mk (rawBlocksLeft (b₀ :: bl'))) T U hT
              (by simp [hU, rawBlocksLeft, rawBlocksRight]) (by rfl)
              (RawBlocksRel.cons hb₀ hbl') hblm hblen hdec hm' hn
          exact ⟨U', hsteps, hrel'⟩
      | @cons b₂ y br' ys hb₂ hbr' =>
          exact simCleanMachine_normal_stmt_step_interior_rawTapeCleanRel M e q q'
            (.move Dir.right) T U (x :: xs) (y :: ys) (b₀ :: bl') (b₂ :: br') a b
            hT hU (RawBlocksRel.cons hb₀ hbl')
            (RawBlocksRel.cons hb₂ hbr') hb hblm
            ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩ hm hn

/-- Left-move case of the normal source step, dispatching on neighbouring block existence. -/
lemma simCleanMachine_normal_stmt_step_move_left {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (hrel : RawTapeCleanRel e T U)
    (hm : M q T.head = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.move Dir.left)) ∧
      RawTapeCleanRel e (T.move Dir.left) U' := by
  rcases hrel with ⟨l, r, bl, br, a, b, hT, hU, hbl, hbr, hb, hblm⟩
  have hm' : M q a = some (q', TM0.Stmt.move Dir.left) := by
    simpa [show T.head = a by rw [hT]; rfl] using hm
  have hblen : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simpa using hblen⟩ = a :=
    hb.choose_spec
  cases hbl with
  | nil =>
      cases hbr with
      | nil =>
          obtain ⟨_, U', _, hsteps, hrel'⟩ :=
            simCleanMachine_move_left_rawTapeCleanRel_both_blank M e q q' a
              b (ListBlank.mk []) T U hT
              (by simp [hU, rawBlocksLeft, rawBlocksRight]) rfl
              hblen hdec hm' hn
          exact ⟨U', hsteps, hrel'⟩
      | @cons b₂ y br' ys hb₂ hbr' =>
          obtain ⟨_, U', _, hsteps, hrel'⟩ :=
            simCleanMachine_move_left_rawTapeCleanRel_blank M e q q' a y
              ys br' b₂ b (ListBlank.mk []) T U hT rfl
              (by simp [hU, rawBlocksLeft, rawBlocksRight]) hbr' hblen
              hdec hb₂ hm' hn
          exact ⟨U', hsteps, hrel'⟩
  | @cons b₀ x bl' xs hb₀ hbl' =>
      cases hbr with
      | nil =>
          have hb₀m : BlockMarked b₀ := (blocksMarked_cons.mp hblm).1
          have hblm' : BlocksMarked bl' := (blocksMarked_cons.mp hblm).2
          have hL : ListBlank.mk (rawBlocksLeft (b₀ :: bl')) =
              ListBlank.append b₀.reverse (ListBlank.mk (rawBlocksLeft bl')) := by
            simp [rawBlocksLeft_cons]
          obtain ⟨_, U', _, hsteps, hrel'⟩ :=
            simCleanMachine_move_left_rawTapeCleanRel_right_blank M e
              q q' a x xs bl' b₀ b (ListBlank.mk (rawBlocksLeft bl'))
              (ListBlank.mk (rawBlocksLeft (b₀ :: bl'))) T U
              hT (by rfl) hL (by simp [hU, rawBlocksRight])
              hbl' hb₀ hb₀m hblm' hblen hdec hm' hn
          exact ⟨U', hsteps, hrel'⟩
      | @cons b₂ y br' ys hb₂ hbr' =>
          exact simCleanMachine_normal_stmt_step_interior_rawTapeCleanRel M e q q'
            (.move Dir.left) T U (x :: xs) (y :: ys) (b₀ :: bl') (b₂ :: br') a b
            hT hU (RawBlocksRel.cons hb₀ hbl')
            (RawBlocksRel.cons hb₂ hbr') hb hblm
            ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩ hm hn

/-! Unified normal-state source-step preservation.  The four endpoint
    combinations are discharged by the quotient-default wrappers above; the
    fully populated case delegates to the interior macro theorem. -/

lemma simCleanMachine_normal_stmt_step {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s : TM0.Stmt Γ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (hrel : RawTapeCleanRel e T U)
    (hm : M q T.head = some (q', s)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (simCleanStmtTime e s) ∧
      RawTapeCleanRel e
        (match s with
        | .write a => T.write a
        | .move d => T.move d) U' := by
  cases s with
  | write z => exact simCleanMachine_normal_stmt_step_write M e q q' z T U hrel hm hn
  | move d =>
      cases d with
      | right => exact simCleanMachine_normal_stmt_step_move_right M e q q' T U hrel hm hn
      | left => exact simCleanMachine_normal_stmt_step_move_left M e q q' T U hrel hm hn


end NPComplete.CookLevin
