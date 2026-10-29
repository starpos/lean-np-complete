module

public import NPComplete.CookLevin.Recode.Sim.TapeRelations

/-!
# Clean simulator microsteps

A simulated operation expands into primitive tape moves, writes, and erasures.
These transition equations let later phase and time arguments reason about the
expanded machine without unfolding its full state function.

Cleanup after the source halts walks over cells that must all be non-blank.
The occupied-tail predicates `SimCleanTailOccupied`/`SimCleanRightTailOccupied`
and `RawTapeCleanOccupiedRel` record that fact alongside the raw-tape relation,
and `simCleanMachine_run_halt_cleanup` runs the cleanup
phase from a halting state to `.final` in a number of steps linear in the
length of the left history.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

lemma simCleanMachine_markMove_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (p : SimPhase e.n Λ) (d : Dir)
    (T : Tape (Option Bool)) :
    TM0.step (simCleanMachine M e)
        ⟨.markMove p d, T⟩ =
      some ⟨.run p, T.move d⟩ := by
  simp [TM0.step, simCleanMachine]


lemma simCleanMachine_run_halt_entry {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (p : SimPhase e.n Λ) (T : Tape (Option Bool))
    (h : simMachine M e p T.head = none) :
    TM0.step (simCleanMachine M e) ⟨.run p, T⟩ =
      some ⟨.rewindLeft, T.write T.head⟩ := by
    simp [TM0.step, simCleanMachine, h]

lemma simCleanMachine_eraseLeft_some_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    {x : Option Bool} (T : Tape (Option Bool))
    (hhead : T.head = x) (hx : x.isSome) :
    TM0.step (simCleanMachine M e) ⟨.eraseLeft, T⟩ =
      some ⟨.eraseLeftMove, T.write none⟩ := by
  simp [TM0.step, simCleanMachine, hhead, hx]

lemma simCleanMachine_eraseLeft_blank_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (T : Tape (Option Bool))
    (hhead : T.head = none) :
    TM0.step (simCleanMachine M e) ⟨.eraseLeft, T⟩ =
      some ⟨.returnMarker, T.move Dir.right⟩ := by
  simp [TM0.step, simCleanMachine, hhead]

lemma simCleanMachine_eraseLeftMove_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (T : Tape (Option Bool)) :
    TM0.step (simCleanMachine M e) ⟨.eraseLeftMove, T⟩ =
      some ⟨.eraseLeft, T.move Dir.left⟩ := by
  simp [TM0.step, simCleanMachine]

lemma simCleanMachine_returnMarker_blank_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (T : Tape (Option Bool))
    (hhead : T.head = none) :
    TM0.step (simCleanMachine M e) ⟨.returnMarker, T⟩ =
      some ⟨.returnMarker, T.move Dir.right⟩ := by
  simp [TM0.step, simCleanMachine, hhead]

lemma simCleanMachine_returnMarker_some_step {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (T : Tape (Option Bool))
    (hhead : T.head.isSome) :
    TM0.step (simCleanMachine M e) ⟨.returnMarker, T⟩ =
      some ⟨.final, T.write T.head⟩ := by
  simp [TM0.step, simCleanMachine, hhead]

lemma simCleanMachine_returnMarker_walk {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (n : ℕ) (x : Option Bool)
    (rs : List (Option Bool)) (hx : x.isSome) :
    StepsTo (TM0.step (simCleanMachine M e))
      ⟨.returnMarker,
        Tape.mk' (ListBlank.mk [])
          (ListBlank.mk (List.replicate n none ++ x :: rs))⟩
      ⟨.final,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs))⟩ (n + 1) := by
  induction n with
  | zero =>
      have hstep := simCleanMachine_returnMarker_some_step M e
        (Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs)))
        (by simpa using hx)
      simpa using (stepsTo_cons _ hstep (stepsTo_zero _ _))
  | succ n ih =>
      let T := Tape.mk' (ListBlank.mk [])
        (ListBlank.mk (List.replicate (n + 1) none ++ x :: rs))
      have hstep := simCleanMachine_returnMarker_blank_step M e T (by
        simp [T, List.replicate_succ])
      have hrest := ih
      have hblank : ListBlank.mk ([none] : List (Option Bool)) =
          ListBlank.mk [] := by
        apply Quotient.sound
        exact Or.inr ⟨1, by simp [default]⟩
      have hrest' : StepsTo (TM0.step (simCleanMachine M e))
          ⟨.returnMarker, T.move Dir.right⟩
          ⟨.final,
            Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs))⟩ (n + 1) := by
        simpa [T, Tape.move, Tape.mk', ListBlank.append,
          List.replicate_succ, List.append_assoc, hblank] using hrest
      have htotal := stepsTo_cons _ hstep hrest'
      simpa [T, Tape.move, Tape.mk', ListBlank.append,
        List.replicate_succ, List.append_assoc, Nat.add_assoc, hblank] using htotal

lemma simCleanMachine_eraseLeft_blank {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (rs : List (Option Bool)) :
    StepsTo (TM0.step (simCleanMachine M e))
      ⟨.eraseLeft,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: rs))⟩
      ⟨.returnMarker,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk rs)⟩ 1 := by
  have hstep := simCleanMachine_eraseLeft_blank_step M e
    (Tape.mk' (ListBlank.mk []) (ListBlank.mk (none :: rs))) rfl
  have hblank : ListBlank.mk ([none] : List (Option Bool)) =
      ListBlank.mk [] := by
    apply Quotient.sound
    exact Or.inr ⟨1, by simp [default]⟩
  simpa [Tape.move, Tape.mk', ListBlank.append, hblank] using
    (stepsTo_cons _ hstep (stepsTo_zero _ _))

lemma simCleanMachine_eraseLeft_nonempty {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (x : Option Bool)
    (xs rs : List (Option Bool)) (hx : x.isSome)
    (hxs : ∀ y ∈ xs, y.isSome) :
    StepsTo (TM0.step (simCleanMachine M e))
      ⟨.eraseLeft,
        Tape.mk' (ListBlank.mk xs) (ListBlank.mk (x :: rs))⟩
      ⟨.returnMarker,
        Tape.mk' (ListBlank.mk [])
          (ListBlank.mk (List.replicate (xs.length + 1) none ++ rs))⟩
      (2 * xs.length + 3) := by
  induction xs generalizing x rs with
  | nil =>
      have h1 := simCleanMachine_eraseLeft_some_step M e
        (x := x) (Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs))) rfl hx
      have h2 := simCleanMachine_eraseLeftMove_step M e
        ((Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs))).write none)
      have h3 := simCleanMachine_eraseLeft_blank_step M e
        (((Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs))).write none).move Dir.left)
        (by simp [Tape.move, Tape.mk', default])
      have htotal := stepsTo_cons _ h1
        (stepsTo_cons _ h2 (stepsTo_cons _ h3 (stepsTo_zero _ _)))
      have hblank : ListBlank.mk ([none] : List (Option Bool)) =
          ListBlank.mk [] := by
        apply Quotient.sound
        exact Or.inr ⟨1, by simp [default]⟩
      simpa [Tape.write_mk', Tape.move, Tape.mk', ListBlank.append,
        List.replicate_succ, Nat.add_assoc, default, hblank] using htotal
  | cons y ys ih =>
      have hy : y.isSome := hxs y (by simp)
      have h1 := simCleanMachine_eraseLeft_some_step M e
        (x := x) (Tape.mk' (ListBlank.mk (y :: ys)) (ListBlank.mk (x :: rs))) rfl hx
      have h2 := simCleanMachine_eraseLeftMove_step M e
        ((Tape.mk' (ListBlank.mk (y :: ys)) (ListBlank.mk (x :: rs))).write none)
      have hrest := ih (x := y) (rs := none :: rs) hy (by
        intro z hz
        exact hxs z (by simp [hz]))
      have hfirst := stepsTo_cons _ h1
        (stepsTo_cons _ h2 (stepsTo_zero _ _))
      have hrest' : StepsTo (TM0.step (simCleanMachine M e))
          ⟨.eraseLeft,
            ((Tape.mk' (ListBlank.mk (y :: ys)) (ListBlank.mk (x :: rs))).write none).move Dir.left⟩
          ⟨.returnMarker,
            Tape.mk' (ListBlank.mk [])
              (ListBlank.mk (List.replicate (ys.length + 1) none ++ none :: rs))⟩
          (2 * ys.length + 3) := by
        simpa [Tape.write_mk', Tape.move, Tape.mk', ListBlank.append,
          List.replicate_succ, List.append_assoc, Nat.add_assoc] using hrest
      have htotal := stepsTo_trans _ hfirst hrest'
      have hshift : ∀ n : Nat,
          none :: List.replicate n none ++ rs =
            List.replicate n none ++ none :: rs := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            simpa [List.replicate_succ] using congrArg (List.cons none) ih
      convert htotal using 1
      simp [Tape.mk', List.replicate_succ, Nat.add_assoc]
      · exact congrArg ListBlank.mk (hshift ys.length)

lemma simCleanMachine_rewindLeft_final {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (x : Option Bool)
    (xs rs : List (Option Bool)) (hx : x.isSome)
    (hxs : ∀ y ∈ xs, y.isSome) :
    StepsTo (TM0.step (simCleanMachine M e))
      ⟨.rewindLeft,
        Tape.mk' (ListBlank.mk xs) (ListBlank.mk (x :: rs))⟩
      ⟨.final,
        Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs))⟩
      (3 * xs.length + 3) := by
  induction xs generalizing x rs with
  | nil =>
      have h1 : TM0.step (simCleanMachine M e)
          ⟨.rewindLeft,
            Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs))⟩ =
          some ⟨.eraseLeft,
            (Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs))).move Dir.left⟩ := by
        simp [TM0.step, simCleanMachine, hx]
      have h2 := simCleanMachine_eraseLeft_blank M e (x :: rs)
      have h3 := simCleanMachine_returnMarker_walk M e 0 x rs hx
      have htotal := stepsTo_cons _ h1 (stepsTo_trans _ h2 h3)
      simpa [Tape.write_mk', Tape.move, Tape.mk', ListBlank.append] using htotal
  | cons y ys ih =>
      have hy : y.isSome := hxs y (by simp)
      have h1 : TM0.step (simCleanMachine M e)
          ⟨.rewindLeft,
            Tape.mk' (ListBlank.mk (y :: ys)) (ListBlank.mk (x :: rs))⟩ =
          some ⟨.eraseLeft,
            (Tape.mk' (ListBlank.mk (y :: ys))
              (ListBlank.mk (x :: rs))).move Dir.left⟩ := by
        simp [TM0.step, simCleanMachine, hx]
      have h2 := simCleanMachine_eraseLeft_nonempty M e y ys
        (x :: rs) hy (by
          intro z hz
          exact hxs z (by simp [hz]))
      have h3 := simCleanMachine_returnMarker_walk M e
        (ys.length + 1) x rs hx
      have htotal := stepsTo_cons _ h1 (stepsTo_trans _ h2 h3)
      convert htotal using 1
      all_goals simp [Nat.add_assoc]
      all_goals omega

lemma simCleanMachine_run_halt_cleanup {Γ Λ : Type} [Inhabited Γ] [Finite Γ]
    [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (p : SimPhase e.n Λ)
    (x : Option Bool) (xs rs : List (Option Bool))
    (hhalt : simMachine M e p x = none) (hx : x.isSome)
    (hxs : ∀ y ∈ xs, y.isSome) :
    StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run p, Tape.mk' (ListBlank.mk xs) (ListBlank.mk (x :: rs))⟩
      ⟨.final, Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs))⟩
      (3 * xs.length + 4) := by
  have hentry := simCleanMachine_run_halt_entry M e p
    (Tape.mk' (ListBlank.mk xs) (ListBlank.mk (x :: rs))) (by
      simpa using hhalt)
  have hrew := simCleanMachine_rewindLeft_final M e x xs rs hx hxs
  have hentry' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run p, Tape.mk' (ListBlank.mk xs) (ListBlank.mk (x :: rs))⟩
      ⟨.rewindLeft,
        (Tape.mk' (ListBlank.mk xs) (ListBlank.mk (x :: rs))).write x⟩ 1 := by
    simpa [Tape.write_self] using
      (stepsTo_cons _ hentry (stepsTo_zero _ _))
  have htotal := stepsTo_trans (t₁ := 1) (t₂ := 3 * xs.length + 3) _
    hentry' hrew
  convert htotal using 1

lemma sim_clean_some_getD_map {xs : List (Option Bool)}
    (hxs : ∀ x ∈ xs, x.isSome) :
    xs.map (fun x => some (x.getD false)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := hxs x (by simp)
      have htail : ∀ y ∈ xs, y.isSome := by
        intro y hy
        exact hxs y (by simp [hy])
      cases x with
      | none => simp at hx
      | some b => simp [ih htail]

def SimCleanTailOccupied (R : ListBlank (Option Bool)) : Prop :=
  ∃ xs : List (Option Bool), R = ListBlank.mk xs ∧ ∀ x ∈ xs, x.isSome

def SimCleanRightTailOccupied {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (U : Tape (Option Bool)) : Prop :=
  SimCleanTailOccupied
    ((Tape.move Dir.right)^[e.n] U).right₀

lemma simCleanTailOccupied_mk
    (xs : List (Option Bool)) (hxs : ∀ x ∈ xs, x.isSome) :
    SimCleanTailOccupied (ListBlank.mk xs) :=
  ⟨xs, rfl, hxs⟩

lemma simCleanTailOccupied_append_mark
    (R : ListBlank (Option Bool)) (hR : SimCleanTailOccupied R)
    (x : Option Bool) (hx : x.isSome) :
    SimCleanTailOccupied (R.tail.cons x) := by
  rcases hR with ⟨xs, hxs, hall⟩
  refine ⟨x :: xs.tail, ?_, ?_⟩
  · rw [hxs]
    simp
  · intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact hall y (List.mem_of_mem_tail hy)

lemma simCleanTailOccupied_append_prefix
    (xs : List (Option Bool)) (R : ListBlank (Option Bool))
    (hxs : ∀ x ∈ xs, x.isSome) (hR : SimCleanTailOccupied R) :
    SimCleanTailOccupied (ListBlank.append xs R) := by
  rcases hR with ⟨ys, hys, hysall⟩
  refine ⟨xs ++ ys, ?_, ?_⟩
  · rw [hys, ListBlank.append_mk]
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hxs z hz
    · exact hysall z hz

lemma simCleanTailOccupied_split_block {n : ℕ}
    (R : ListBlank (Option Bool))
    (hR : SimCleanTailOccupied R) :
    ∃ b tail : List (Option Bool),
      b.length = n ∧ R = ListBlank.append b (ListBlank.mk tail) ∧
        ∀ x ∈ tail, x.isSome := by
  rcases hR with ⟨xs, hxs, hall⟩
  by_cases hlen : n ≤ xs.length
  · let b := xs.take n
    let tail := xs.drop n
    have hsplit : b ++ tail = xs := by
      exact List.take_append_drop n xs
    have hblen : b.length = n := by
      simp [b, hlen]
    have hR' : R = ListBlank.append b (ListBlank.mk tail) := by
      rw [hxs, ListBlank.append_mk, hsplit]
    have htail : ∀ x ∈ tail, x.isSome := by
      intro x hx
      exact hall x (List.mem_of_mem_drop hx)
    exact ⟨b, tail, hblen, hR', htail⟩
  · have hshort : xs.length ≤ n := by omega
    let b := xs ++ List.replicate (n - xs.length) none
    let tail : List (Option Bool) := []
    have hblen : b.length = n := by
      simp [b]
      omega
    have hR' : R = ListBlank.append b (ListBlank.mk tail) := by
      rw [hxs, ListBlank.append_mk]
      simp only [b, tail, List.append_nil]
      apply (listBlank_mk_append_all_none xs
        (List.replicate (n - xs.length) none) ?_).symm
      intro x hx
      simp at hx
      exact hx.2
    have htail : ∀ x ∈ tail, x.isSome := by
      intro x hx
      simp [tail] at hx
    exact ⟨b, tail, hblen, hR', htail⟩

lemma simCleanRightTailOccupied_split {Γ : Type} [Inhabited Γ]
    [Finite Γ] (e : BlockEnc Γ) (L : ListBlank (Option Bool))
    (b : List (Option Bool)) (R : ListBlank (Option Bool))
    (U : Tape (Option Bool)) (hb : b.length = e.n)
    (hU : U = Tape.mk' L (ListBlank.append b R))
    (hocc : SimCleanRightTailOccupied e U) :
    SimCleanTailOccupied R := by
  rcases hocc with ⟨xs, hxs, hall⟩
  refine ⟨xs, ?_, hall⟩
  have hmove : ((Tape.move Dir.right)^[e.n] U).right₀ = R := by
    rw [hU, ← hb, tape_move_right_block b L R]
    simp
  exact hmove.symm.trans hxs

lemma simCleanRightTailOccupied_of_split {Γ : Type} [Inhabited Γ]
    [Finite Γ] (e : BlockEnc Γ) (L : ListBlank (Option Bool))
    (b : List (Option Bool)) (R : ListBlank (Option Bool))
    (U : Tape (Option Bool)) (hb : b.length = e.n)
    (hU : U = Tape.mk' L (ListBlank.append b R))
    (hR : SimCleanTailOccupied R) :
    SimCleanRightTailOccupied e U := by
  rcases hR with ⟨xs, hxs, hall⟩
  refine ⟨xs, ?_, hall⟩
  have hmove : ((Tape.move Dir.right)^[e.n] U).right₀ = R := by
    rw [hU, ← hb, tape_move_right_block b L R]
    simp
  exact hmove.trans hxs

lemma simCleanRightTailOccupied_mk₁ {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (xs : List (Option Bool))
    (hxs : ∀ x ∈ xs, x.isSome) :
    SimCleanRightTailOccupied e (Tape.mk₁ xs) := by
  let tail : List (Option Bool) := xs.drop e.n
  refine ⟨tail, ?_, ?_⟩
  · have hmove : ∀ n (L : ListBlank (Option Bool))
        (ys : List (Option Bool)),
        ((Tape.move Dir.right)^[n] (Tape.mk' L (ListBlank.mk ys))).right₀ =
          ListBlank.mk (ys.drop n) := by
      intro n
      induction n with
      | zero =>
          intro L ys
          simpa [Tape.right₀, Tape.mk'] using
            (ListBlank.cons_head_tail (ListBlank.mk ys))
      | succ n ih =>
          intro L ys
          rw [Function.iterate_succ_apply]
          cases ys with
          | nil =>
              simpa [Tape.mk', Tape.move, ListBlank.tail_mk] using
                ih (L.cons default) []
          | cons y ys =>
              simpa [Tape.mk', Tape.move] using ih (L.cons y) ys
    exact hmove e.n (ListBlank.mk []) xs
  · intro x hx
    exact hxs x (List.mem_of_mem_drop hx)

lemma stepsTo_endpoint_eq {α : Type} {f : α → Option α}
    {a b c : α} {t : ℕ}
    (h₁ : StepsTo f a b t) (h₂ : StepsTo f a c t) : b = c := by
  unfold StepsTo at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

def RawTapeCleanOccupiedRel {Γ : Type} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (T : Tape Γ) (U : Tape (Option Bool)) : Prop :=
  RawTapeCleanRel e T U ∧ SimCleanRightTailOccupied e U

lemma simCleanMachine_marked_halt_cleanup_rep {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (p : SimPhase e.n Λ)
    (old : List (Option Bool)) (L R : ListBlank (Option Bool))
    (ls : List (Option Bool))
    (hold : old.length = e.n) (hmarked : BlockMarked old)
    (hL : L = ListBlank.mk ls ∧ ∀ x ∈ ls, x.isSome)
    (hR : SimCleanTailOccupied R)
    (hhalt : simMachine M e p old.headI = none) (hn : 0 < e.n) :
    ∃ out : List Bool,
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run p, Tape.mk' L
          (ListBlank.append old R)⟩
      ⟨.final, Tape.mk₁ (tapeSymbols out)⟩
        (3 * ls.length + 4) ∧
      e.decodeFirst out =
        e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ ∧
      ∃ rs, R = ListBlank.mk rs ∧
        (∀ x ∈ rs, x.isSome) ∧
        out = (old ++ rs).map (Option.getD · false) := by
  have hne : old ≠ [] := by
    intro hnil
    have hzero : e.n = 0 := by simpa [hnil] using hold.symm
    omega
  obtain ⟨x, xs, hcons⟩ := List.exists_cons_of_ne_nil hne
  subst old
  have hx : x.isSome := hmarked x (by simp)
  have hxs : ∀ y ∈ xs, y.isSome := by
    intro y hy
    exact hmarked y (by simp [hy])
  rcases hL with ⟨hLmk, hls⟩
  rcases hR with ⟨rs, hRmk, hrs⟩
  let rs' : List (Option Bool) := xs ++ rs
  let out : List Bool := (x :: rs').map (Option.getD · false)
  have hclean := simCleanMachine_run_halt_cleanup M e p x ls rs'
    hhalt hx hls
  have hstart : Tape.mk' (ListBlank.mk ls)
      (ListBlank.append (x :: xs) R) =
      Tape.mk' (ListBlank.mk ls) (ListBlank.mk (x :: rs')) := by
    rw [hRmk]
    simp [rs']
  have hclean' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run p, Tape.mk' L
        (ListBlank.append (x :: xs) R)⟩
      ⟨.final, Tape.mk' (ListBlank.mk []) (ListBlank.mk (x :: rs'))⟩
      (3 * ls.length + 4) := by
    rw [hLmk]
    rw [hstart]
    simpa [hLmk] using hclean
  have houtSome : ∀ y ∈ x :: rs', y.isSome := by
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · simp only [rs', List.mem_append] at hy
      rcases hy with hy | hy
      · exact hxs y hy
      · exact hrs y hy
  have hcanon : Tape.mk' (ListBlank.mk [])
      (ListBlank.mk (x :: rs')) = Tape.mk₁ (tapeSymbols out) := by
    simp only [Tape.mk₁, Tape.mk₂]
    rw [← sim_clean_some_getD_map houtSome]
    simp [tapeSymbols, out, Function.comp_def]
  refine ⟨out, ?_⟩
  rw [hcanon] at hclean'
  refine ⟨hclean', ?_, ?_⟩
  · simpa [out, rs'] using
      (BlockEnc.decodeFirst_of_blockDecodes e (x :: xs) rs
      (e.dec ⟨(x :: xs).map (Option.getD · false), by
        simpa only [List.length_map, List.length_cons] using hold⟩)
      hold rfl)
  · exact ⟨rs, hRmk, hrs, by simp [out, rs']⟩


end NPComplete.CookLevin
