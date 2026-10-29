module

public import NPComplete.CookLevin.Machines.DropSupport

/-!
The trailing-false machine is separated from packed decoding so its output
semantics and polynomial bound can be reused without importing decoder proofs.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_trans)

def dropTrailingFalse (xs : List Bool) : List Bool :=
  (xs.reverse.dropWhile (fun b => !b)).reverse

lemma dropWhile_false_reverse (tail : List Bool)
    (htail : ∀ b ∈ tail, b = false) :
    tail.reverse.dropWhile (fun b => !b) = [] := by
  induction tail with
  | nil => simp
  | cons b tail ih =>
      have hb : b = false := htail b (by simp)
      subst b
      have htail' : ∀ b ∈ tail, b = false := by
        intro b hb
        exact htail b (by simp [hb])
      rw [List.reverse_cons, List.dropWhile_append, ih htail']
      simp

lemma dropTrailingFalse_append_false {pre tail : List Bool}
    (hpre : pre = [] ∨ ∃ ys, pre = ys ++ [true])
    (htail : ∀ b ∈ tail, b = false) :
    dropTrailingFalse (pre ++ tail) = pre := by
  rcases hpre with rfl | ⟨ys, rfl⟩
  · simp [dropTrailingFalse, dropWhile_false_reverse tail htail]
  · have hdrop := dropWhile_false_reverse tail htail
    unfold dropTrailingFalse
    rw [List.reverse_append, List.dropWhile_append, hdrop]
    simp

inductive DropTrailingFalsePhase
  | seekEnd
  | trim
  | trimMove
  | rewind
  | done
  deriving DecidableEq

instance : Inhabited DropTrailingFalsePhase := ⟨.seekEnd⟩

def dropTrailingFalseMachine : TM0.Machine (Option Bool) DropTrailingFalsePhase
  | .seekEnd, none => some (.trim, .move Dir.left)
  | .seekEnd, some _ => some (.seekEnd, .move Dir.right)
  | .trim, none => some (.done, .write none)
  | .trim, some false => some (.trimMove, .write none)
  | .trim, some true => some (.rewind, .move Dir.left)
  | .trimMove, _ => some (.trim, .move Dir.left)
  | .rewind, some _ => some (.rewind, .move Dir.left)
  | .rewind, none => some (.done, .move Dir.right)
  | .done, _ => none

def dropTrailingFalseSupport : Finset DropTrailingFalsePhase :=
  {.seekEnd, .trim, .trimMove, .rewind, .done}

lemma dropTrailingFalseMachine_supports :
    TM0.Supports dropTrailingFalseMachine (↑dropTrailingFalseSupport) := by
  refine ⟨?_, ?_⟩
  · change DropTrailingFalsePhase.seekEnd ∈
      (↑dropTrailingFalseSupport : Set DropTrailingFalsePhase)
    simp [dropTrailingFalseSupport]
  · intro q a q' s hstep hmem
    cases q with
    | seekEnd =>
        cases a with
        | none =>
            simp [dropTrailingFalseMachine] at hstep
            rcases hstep with ⟨rfl, _⟩
            simp [dropTrailingFalseSupport]
        | some val =>
            simp [dropTrailingFalseMachine] at hstep
            rcases hstep with ⟨rfl, _⟩
            simp [dropTrailingFalseSupport]
    | trim =>
        cases a with
        | none =>
            simp [dropTrailingFalseMachine] at hstep
            rcases hstep with ⟨rfl, _⟩
            simp [dropTrailingFalseSupport]
        | some val =>
            cases val <;>
              simp [dropTrailingFalseMachine] at hstep ⊢ <;>
              rcases hstep with ⟨rfl, _⟩ <;>
              simp [dropTrailingFalseSupport]
    | trimMove =>
        simp [dropTrailingFalseMachine] at hstep
        rcases hstep with ⟨rfl, _⟩
        simp [dropTrailingFalseSupport]
    | rewind =>
        cases a with
        | none =>
            simp [dropTrailingFalseMachine] at hstep
            rcases hstep with ⟨rfl, _⟩
            simp [dropTrailingFalseSupport]
        | some val =>
            simp [dropTrailingFalseMachine] at hstep
            rcases hstep with ⟨rfl, _⟩
            simp [dropTrailingFalseSupport]
    | done =>
        simp [dropTrailingFalseMachine] at hstep

def dropTape (left right : List Bool) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk (left.map some))
    (ListBlank.mk (right.map some ++ [none]))

def dropBlank (right : List Bool) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk [])
    (ListBlank.mk (none :: right.map some ++ [none]))

lemma dropTape_start (xs : List Bool) :
    dropTape [] xs = Tape.mk₁ (tapeSymbols xs) := by
  simp only [dropTape, Tape.mk₁, Tape.mk₂, tapeSymbols]
  apply congrArg (fun R => Tape.mk' (ListBlank.mk []) R)
  apply Quotient.sound'
  exact Or.inr ⟨1, by simp [default]⟩

lemma dropTape_move_right (left : List Bool) (x : Bool) (right : List Bool) :
    (dropTape left (x :: right)).move Dir.right = dropTape (x :: left) right := by
  simp [dropTape, Tape.move_right_mk', ListBlank.cons_mk]

lemma dropTape_move_left (left : List Bool) (x : Bool) (right : List Bool) :
    (dropTape (x :: left) right).move Dir.left = dropTape left (x :: right) := by
  simp [dropTape, Tape.move_left_mk', ListBlank.cons_mk]

lemma dropTape_empty_move_left (right : List Bool) :
    (dropTape [] right).move Dir.left = dropBlank right := by
  simp [dropTape, dropBlank, Tape.move_left_mk', ListBlank.cons_mk, default]

lemma dropBlank_move_right (right : List Bool) :
    (dropBlank right).move Dir.right = dropTape [] right := by
  simp only [dropBlank, dropTape, Tape.move_right_mk', ListBlank.cons_mk,
    ListBlank.head_mk, ListBlank.tail_mk]
  change Tape.mk' (ListBlank.mk [none])
      (ListBlank.mk (List.map some right ++ [none])) =
    Tape.mk' (ListBlank.mk [])
      (ListBlank.mk (List.map some right ++ [none]))
  apply congrArg₂ Tape.mk'
  · exact Quotient.sound' (Or.inr ⟨1, by simp [default]⟩)
  · rfl

lemma dropTape_head_some (left right : List Bool) (x : Bool) :
    (dropTape left (x :: right)).head = some x := by
  rfl

lemma dropBlank_head_none (right : List Bool) :
    (dropBlank right).head = none := by
  rfl

lemma dropBlank_write_none (right : List Bool) :
    (dropBlank right).write none = dropBlank right := by
  simp [dropBlank, Tape.write_mk']

lemma dropBlank_empty : dropBlank [] = dropTape [] [] := by
  simp only [dropBlank, dropTape]
  change Tape.mk' (ListBlank.mk []) (ListBlank.mk [none, none]) =
    Tape.mk' (ListBlank.mk []) (ListBlank.mk [none])
  apply congrArg (fun R => Tape.mk' (ListBlank.mk []) R)
  exact Quotient.sound' (Or.inr ⟨1, by simp [default]⟩)

lemma dropTape_erase_false_move_left (left : List Bool) (x : Bool) :
    ((dropTape (x :: left) [false]).write none).move Dir.left =
      dropTape left [x] := by
  simp only [dropTape, Tape.write_mk', Tape.move_left_mk', ListBlank.cons_mk,
    ListBlank.head_mk, ListBlank.tail_mk]
  change Tape.mk' (ListBlank.mk (List.map some left))
      (ListBlank.mk (some x :: none :: [none])) =
    Tape.mk' (ListBlank.mk (List.map some left))
      (ListBlank.mk (some x :: [none]))
  apply congrArg (fun R => Tape.mk' (ListBlank.mk (List.map some left)) R)
  exact Quotient.sound' (Or.inr ⟨1, by simp [default]⟩)

lemma dropTape_empty_erase_move_left :
    ((dropTape [] [false]).write none).move Dir.left = dropBlank [] := by
  simp only [dropTape, dropBlank, Tape.write_mk', Tape.move_left_mk',
    ListBlank.cons_mk, ListBlank.head_mk, ListBlank.tail_mk]
  change Tape.mk' (ListBlank.mk []) (ListBlank.mk [none, none, none]) =
    Tape.mk' (ListBlank.mk []) (ListBlank.mk [none, none])
  apply congrArg (fun R => Tape.mk' (ListBlank.mk []) R)
  exact Quotient.sound' (Or.inr ⟨1, by simp [default]⟩)

lemma drop_step_seek_some (T : Tape (Option Bool)) (b : Bool)
    (h : T.head = some b) :
    TM0.step dropTrailingFalseMachine ⟨.seekEnd, T⟩ =
      some ⟨.seekEnd, T.move Dir.right⟩ := by
  simp only [TM0.step]
  rw [h]
  rfl

lemma drop_step_seek_none (T : Tape (Option Bool)) (h : T.head = none) :
    TM0.step dropTrailingFalseMachine ⟨.seekEnd, T⟩ =
      some ⟨.trim, T.move Dir.left⟩ := by
  simp only [TM0.step]
  rw [h]
  rfl

lemma drop_step_trim_false (T : Tape (Option Bool))
    (h : T.head = some false) :
    TM0.step dropTrailingFalseMachine ⟨.trim, T⟩ =
      some ⟨.trimMove, T.write none⟩ := by
  simp only [TM0.step]
  rw [h]
  rfl

lemma drop_step_trim_true (T : Tape (Option Bool))
    (h : T.head = some true) :
    TM0.step dropTrailingFalseMachine ⟨.trim, T⟩ =
      some ⟨.rewind, T.move Dir.left⟩ := by
  simp only [TM0.step]
  rw [h]
  rfl

lemma drop_step_trim_none (T : Tape (Option Bool))
    (h : T.head = none) :
    TM0.step dropTrailingFalseMachine ⟨.trim, T⟩ =
      some ⟨.done, T.write none⟩ := by
  simp only [TM0.step]
  rw [h]
  rfl

lemma drop_step_trimMove (T : Tape (Option Bool)) :
    TM0.step dropTrailingFalseMachine ⟨.trimMove, T⟩ =
      some ⟨.trim, T.move Dir.left⟩ := by
  simp only [TM0.step]
  rfl

lemma drop_step_rewind_some (T : Tape (Option Bool)) (b : Bool)
    (h : T.head = some b) :
    TM0.step dropTrailingFalseMachine ⟨.rewind, T⟩ =
      some ⟨.rewind, T.move Dir.left⟩ := by
  simp only [TM0.step]
  rw [h]
  rfl

lemma drop_step_rewind_none (T : Tape (Option Bool))
    (h : T.head = none) :
    TM0.step dropTrailingFalseMachine ⟨.rewind, T⟩ =
      some ⟨.done, T.move Dir.right⟩ := by
  simp only [TM0.step]
  rw [h]
  rfl

lemma drop_scan (left xs : List Bool) :
    StepsTo (TM0.step dropTrailingFalseMachine)
      ⟨.seekEnd, dropTape left xs⟩
      ⟨.seekEnd, dropTape (xs.reverse ++ left) []⟩ xs.length := by
  induction xs generalizing left with
  | nil => exact stepsTo_zero _ _
  | cons x xs ih =>
      have hs : TM0.step dropTrailingFalseMachine
          ⟨.seekEnd, dropTape left (x :: xs)⟩ =
          some ⟨.seekEnd, dropTape (x :: left) xs⟩ := by
        rw [drop_step_seek_some _ x (dropTape_head_some left xs x)]
        rw [dropTape_move_right]
      have hi := ih (left := x :: left)
      rw [List.reverse_cons]
      simpa [List.append_assoc] using stepsTo_cons _ hs hi

lemma drop_rewind (left right : List Bool) (hright : right ≠ []) :
    ∃ k, k ≤ left.length + 2 ∧
      StepsTo (TM0.step dropTrailingFalseMachine)
        ⟨.rewind, dropTape left right⟩
        ⟨.done, dropTape [] (left.reverse ++ right)⟩ k := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact (hright rfl).elim
      | cons b rest =>
          have hs1 : TM0.step dropTrailingFalseMachine
              ⟨.rewind, dropTape [] (b :: rest)⟩ =
              some ⟨.rewind, dropBlank (b :: rest)⟩ := by
            rw [drop_step_rewind_some _ b (dropTape_head_some [] rest b)]
            rw [dropTape_empty_move_left]
          have hs2 : TM0.step dropTrailingFalseMachine
              ⟨.rewind, dropBlank (b :: rest)⟩ =
              some ⟨.done, dropTape [] (b :: rest)⟩ := by
            rw [drop_step_rewind_none _ (dropBlank_head_none _)]
            rw [dropBlank_move_right]
          refine ⟨2, by simp, ?_⟩
          simpa using stepsTo_cons _ hs1
            (stepsTo_cons _ hs2 (stepsTo_zero _ _))
  | cons x left ih =>
      obtain ⟨b, rest, hrightEq⟩ := List.exists_cons_of_ne_nil hright
      subst right
      have hs : TM0.step dropTrailingFalseMachine
          ⟨.rewind, dropTape (x :: left) (b :: rest)⟩ =
          some ⟨.rewind, dropTape left (x :: b :: rest)⟩ := by
        rw [drop_step_rewind_some _ b
          (dropTape_head_some (x :: left) rest b)]
        rw [dropTape_move_left]
      obtain ⟨k, hk, hsteps⟩ := ih (right := x :: b :: rest) (by simp)
      refine ⟨k + 1, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · rw [List.reverse_cons]
        simpa [List.append_assoc] using stepsTo_cons _ hs hsteps

lemma drop_trim_end (pre : List Bool) (last : Bool) :
    ∃ k, k ≤ 2 * pre.length + 3 ∧
      StepsTo (TM0.step dropTrailingFalseMachine)
        ⟨.trim, dropTape pre.reverse [last]⟩
        ⟨.done, dropTape [] (dropTrailingFalse (pre ++ [last]))⟩ k := by
  revert last
  induction pre using List.reverseRecOn with
  | nil =>
      intro last
      cases last with
      | false =>
          have hs1 : TM0.step dropTrailingFalseMachine
              ⟨.trim, dropTape [] [false]⟩ =
              some ⟨.trimMove, (dropTape [] [false]).write none⟩ := by
            rw [drop_step_trim_false _ (dropTape_head_some [] [] false)]
          have hs2 : TM0.step dropTrailingFalseMachine
              ⟨.trimMove, (dropTape [] [false]).write none⟩ =
              some ⟨.trim, dropBlank []⟩ := by
            rw [drop_step_trimMove]
            rw [dropTape_empty_erase_move_left]
          have hs3 : TM0.step dropTrailingFalseMachine
              ⟨.trim, dropBlank []⟩ =
              some ⟨.done, (dropBlank []).write none⟩ := by
            rw [drop_step_trim_none _ (dropBlank_head_none _)]
          have hfinal : (dropBlank []).write none = dropTape [] [] :=
            (dropBlank_write_none []).trans dropBlank_empty
          refine ⟨3, by simp, ?_⟩
          rw [hfinal] at hs3
          simpa [dropTape_start, dropTrailingFalse] using
            stepsTo_cons _ hs1 (stepsTo_cons _ hs2 (stepsTo_cons _ hs3
              (stepsTo_zero _ _)))
      | true =>
          have hs1 : TM0.step dropTrailingFalseMachine
              ⟨.trim, dropTape [] [true]⟩ =
              some ⟨.rewind, dropBlank [true]⟩ := by
            rw [drop_step_trim_true _ (dropTape_head_some [] [] true)]
            rw [dropTape_empty_move_left]
          have hs2 : TM0.step dropTrailingFalseMachine
              ⟨.rewind, dropBlank [true]⟩ =
              some ⟨.done, dropTape [] [true]⟩ := by
            rw [drop_step_rewind_none _ (dropBlank_head_none _)]
            rw [dropBlank_move_right]
          refine ⟨2, by simp, ?_⟩
          simpa [dropTape_start, dropTrailingFalse] using
            stepsTo_cons _ hs1 (stepsTo_cons _ hs2 (stepsTo_zero _ _))
  | append_singleton pre x ih =>
      intro last
      cases last with
      | false =>
          have hs1 : TM0.step dropTrailingFalseMachine
              ⟨.trim, dropTape (x :: pre.reverse) [false]⟩ =
              some ⟨.trimMove,
                (dropTape (x :: pre.reverse) [false]).write none⟩ := by
            rw [drop_step_trim_false _
              (dropTape_head_some (x :: pre.reverse) [] false)]
          have hs2 : TM0.step dropTrailingFalseMachine
              ⟨.trimMove,
                (dropTape (x :: pre.reverse) [false]).write none⟩ =
              some ⟨.trim, dropTape pre.reverse [x]⟩ := by
            rw [drop_step_trimMove]
            rw [dropTape_erase_false_move_left]
          obtain ⟨k, hk, hsteps⟩ := ih x
          refine ⟨k + 2, ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · simpa [List.reverse_append, dropTrailingFalse] using
              stepsTo_cons _ hs1 (stepsTo_cons _ hs2 hsteps)
      | true =>
          have hs1 : TM0.step dropTrailingFalseMachine
              ⟨.trim, dropTape (x :: pre.reverse) [true]⟩ =
              some ⟨.rewind, dropTape pre.reverse [x, true]⟩ := by
            rw [drop_step_trim_true _
              (dropTape_head_some (x :: pre.reverse) [] true)]
            rw [dropTape_move_left]
          obtain ⟨k, hk, hsteps⟩ := drop_rewind pre.reverse [x, true] (by simp)
          refine ⟨k + 1, ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            have hprelen : pre.reverse.length = pre.length := by simp
            omega
          · rw [List.reverse_append]
            simpa [List.reverse_reverse, List.append_assoc, dropTrailingFalse] using
              stepsTo_cons _ hs1 hsteps

lemma dropTrailingFalse_steps (xs : List Bool) :
    ∃ k, k ≤ 3 * xs.length + 2 ∧
      StepsTo (TM0.step dropTrailingFalseMachine)
        ⟨.seekEnd, Tape.mk₁ (tapeSymbols xs)⟩
        ⟨.done, Tape.mk₁ (tapeSymbols (dropTrailingFalse xs))⟩ k := by
  induction xs using List.reverseRecOn with
  | nil =>
      have hs1 : TM0.step dropTrailingFalseMachine
          ⟨.seekEnd, dropTape [] []⟩ =
          some ⟨.trim, (dropTape [] []).move Dir.left⟩ := by
        rw [drop_step_seek_none _ (by rfl)]
      have hs3 : TM0.step dropTrailingFalseMachine
          ⟨.trim, dropBlank []⟩ =
          some ⟨.done, (dropBlank []).write none⟩ := by
        rw [drop_step_trim_none _ (dropBlank_head_none _)]
      have hfinal : (dropBlank []).write none = dropTape [] [] :=
        (dropBlank_write_none []).trans dropBlank_empty
      refine ⟨2, by simp, ?_⟩
      rw [dropTape_empty_move_left] at hs1
      rw [hfinal] at hs3
      simpa [dropTape_start, dropTrailingFalse] using
        stepsTo_cons _ hs1 (stepsTo_cons _ hs3 (stepsTo_zero _ _))
  | append_singleton rest last =>
      have hs : StepsTo (TM0.step dropTrailingFalseMachine)
          ⟨.seekEnd, dropTape [] (rest ++ [last])⟩
          ⟨.seekEnd, dropTape (rest ++ [last]).reverse []⟩
          (rest ++ [last]).length := by
        simpa only [List.append_nil] using drop_scan [] (rest ++ [last])
      have hblank : TM0.step dropTrailingFalseMachine
          ⟨.seekEnd,
            dropTape ((rest ++ [last]).reverse) []⟩ =
          some ⟨.trim,
            (dropTape ((rest ++ [last]).reverse) []).move Dir.left⟩ := by
        rw [drop_step_seek_none _ (by rfl)]
      have hmove :
          (dropTape ((rest ++ [last]).reverse) []).move Dir.left =
            dropTape rest.reverse [last] := by
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
        rw [dropTape_move_left]
      rw [hmove] at hblank
      obtain ⟨kt, htbound, ht⟩ := drop_trim_end rest last
      have hchain := stepsTo_trans _ hs (stepsTo_cons _ hblank ht)
      refine ⟨kt + 1 + (rest ++ [last]).length, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · simpa [dropTape_start, List.reverse_append, List.reverse_reverse,
          List.append_assoc] using hchain

noncomputable def dropTrailingFalseAux : TM0ComputableAux Bool where
  Λ := DropTrailingFalsePhase
  M := dropTrailingFalseMachine
  S := dropTrailingFalseSupport
  supports := dropTrailingFalseMachine_supports

noncomputable def dropTrailingFalseTime : Polynomial ℕ := 3 * X + 2

noncomputable def dropTrailingFalseComputableInPolyTime :
    TM0ComputableInPolyTime (fun l : List Bool => l) (fun l : List Bool => l)
      dropTrailingFalse where
  toTM0ComputableAux := dropTrailingFalseAux
  time := dropTrailingFalseTime
  outputsFun raw := by
    obtain ⟨k, hk, hsteps⟩ := dropTrailingFalse_steps raw
    refine ⟨.done, k, ?_, ?_, ?_⟩
    · simpa [dropTrailingFalseTime] using hk
    · change StepsTo (TM0.step dropTrailingFalseMachine)
        ⟨.seekEnd, Tape.mk₁ (tapeSymbols raw)⟩
        ⟨.done, Tape.mk₁ (tapeSymbols (dropTrailingFalse raw))⟩ k
      exact hsteps
    · change TM0.step dropTrailingFalseMachine
        ⟨.done, Tape.mk₁ (tapeSymbols (dropTrailingFalse raw))⟩ = none
      rfl

end NPComplete.CookLevin
