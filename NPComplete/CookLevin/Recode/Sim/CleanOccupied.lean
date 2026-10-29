module

public import NPComplete.CookLevin.Recode.Sim.CleanContent

/-!
# Occupied-tail simulation

The clean simulator must retain a nonempty right tail as well as decoded content,
because cleanup and movement depend on that invariant. These lemmas strengthen
content preservation across exactly the transitions where occupancy is needed.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

lemma simCleanMachine_normal_stmt_step_occupied {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s : TM0.Stmt Γ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (hrel : RawTapeCleanRel e T U)
    (hocc : SimCleanRightTailOccupied e U)
    (hm : M q T.head = some (q', s)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩ (simCleanStmtTime e s) ∧
      RawTapeCleanOccupiedRel e
        (match s with
        | .write a => T.write a
        | .move d => T.move d) U' := by
  obtain ⟨U₂, hsteps₂, hrel₂⟩ :=
    simCleanMachine_normal_stmt_step M e q q' s T U hrel hm hn
  rcases hrel with ⟨l, r, bl, br, a, b, hT, hU,
    hbl, hbr, hb, hblm⟩
  have hhead : T.head = a := by
    rw [hT]
    rfl
  have hm' : M q a = some (q', s) := by
    simpa [hhead] using hm
  have hold : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simp [hold]⟩ = a :=
    hb.choose_spec
  let L : ListBlank (Option Bool) := ListBlank.mk (rawBlocksLeft bl)
  let R : ListBlank (Option Bool) := ListBlank.mk (rawBlocksRight br)
  have hU' : U = Tape.mk' L (ListBlank.append b R) := by
    simp [L, R, hU]
  have hRocc : SimCleanTailOccupied R := by
    exact simCleanRightTailOccupied_split e L b R U hold hU' hocc
  have hocc' : SimCleanRightTailOccupied e
      (Tape.mk' L (ListBlank.append b R)) := by
    exact simCleanRightTailOccupied_of_split e L b R
      (Tape.mk' L (ListBlank.append b R)) hold rfl hRocc
  cases s with
  | write z =>
      obtain ⟨bits, U', hbits, hsteps, hocc'⟩ :=
        simCleanMachine_partial_write_macro_occupied M e q q' z a
          b L R hold hdec hm' hn hocc'
      rw [← hU'] at hsteps
      have heq : U₂ = U' := by
        have hc := stepsTo_endpoint_eq hsteps₂ hsteps
        cases hc
        rfl
      have hocc₂ : SimCleanRightTailOccupied e U₂ := by
        rw [heq]
        exact hocc'
      exact ⟨U₂, hsteps₂, ⟨by simpa using hrel₂, hocc₂⟩⟩
  | move d =>
      cases d with
      | right =>
          obtain ⟨bits, U', hbits, hsteps, hocc'⟩ :=
            simCleanMachine_partial_move_right_macro_occupied_of_tail M e
              q q' a b L R hold hdec hm' hn hRocc
          rw [← hU'] at hsteps
          have heq : U₂ = U' := by
            have hc := stepsTo_endpoint_eq hsteps₂ hsteps
            cases hc
            rfl
          have hocc₂ : SimCleanRightTailOccupied e U₂ := by
            rw [heq]
            exact hocc'
          exact ⟨U₂, hsteps₂, ⟨by simpa using hrel₂, hocc₂⟩⟩
      | left =>
          cases bl with
          | nil =>
              let b₀ : List (Option Bool) := List.replicate e.n none
              let L₀ : ListBlank (Option Bool) := ListBlank.mk []
              have hb₀ : b₀.length = e.n := by simp [b₀]
              have hL : L = ListBlank.append b₀.reverse L₀ := by
                have hblank : ListBlank.mk b₀.reverse = ListBlank.mk [] := by
                  apply listBlank_mk_append_all_none [] b₀.reverse
                  intro x hx
                  simp [b₀] at hx
                  exact hx.2
                simpa [L, L₀, b₀, rawBlocksLeft, ListBlank.append] using
                  hblank.symm
              obtain ⟨bits, U', hbits, hsteps, hocc'⟩ :=
                simCleanMachine_partial_move_left_macro_occupied M e q q' a
                  b b₀ L₀ L R hold hdec hm' hn
                  hb₀ hL hRocc
              rw [← hU'] at hsteps
              have heq : U₂ = U' := by
                have hc := stepsTo_endpoint_eq hsteps₂ hsteps
                cases hc
                rfl
              have hocc₂ : SimCleanRightTailOccupied e U₂ := by
                rw [heq]
                exact hocc'
              exact ⟨U₂, hsteps₂, ⟨by simpa using hrel₂, hocc₂⟩⟩
          | cons b₀ bl' =>
              cases hbl with
              | cons hb₀ hbl' =>
                  let L₀ : ListBlank (Option Bool) :=
                    ListBlank.mk (rawBlocksLeft bl')
                  have hL : L = ListBlank.append b₀.reverse L₀ := by
                    simp [L, L₀, rawBlocksLeft_cons]
                  have hb₀len : b₀.length = e.n := blockDecodes_length hb₀
                  obtain ⟨bits, U', hbits, hsteps, hocc'⟩ :=
                    simCleanMachine_partial_move_left_macro_occupied M e q q' a
                      b b₀ L₀ L R hold hdec hm' hn hb₀len hL hRocc
                  rw [← hU'] at hsteps
                  have heq : U₂ = U' := by
                    have hc := stepsTo_endpoint_eq hsteps₂ hsteps
                    cases hc
                    rfl
                  have hocc₂ : SimCleanRightTailOccupied e U₂ := by
                    rw [heq]
                    exact hocc'
                  exact ⟨U₂, hsteps₂, ⟨by simpa using hrel₂, hocc₂⟩⟩

lemma simCleanMachine_partial_halt_macro_rep {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q : Λ) (a : Γ)
    (old : List (Option Bool)) (L R : ListBlank (Option Bool))
    (ls : List (Option Bool))
    (hold : old.length = e.n)
    (hdec : e.dec ⟨old.map (Option.getD · false), by simp [hold]⟩ = a)
    (hm : M q a = none) (hn : 0 < e.n)
    (hL : L = ListBlank.mk ls ∧ ∀ x ∈ ls, x.isSome)
    (hR : SimCleanTailOccupied R) :
    ∃ out : List Bool,
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
      ⟨.final, Tape.mk₁ (tapeSymbols out)⟩
        (3 * e.n + 3 * ls.length + 7) ∧
      e.decodeFirst out = a ∧
      ∃ rs, simCleanPartialWriteTail e old L R = ListBlank.mk rs ∧
        (∀ x ∈ rs, x.isSome) ∧
        out = (simMarkBlock old ++ rs).map (Option.getD · false) := by
  obtain ⟨bits, hbits, hread⟩ := simCleanMachine_read_rewind_any M e q
    old L R hold hn
  let oldM : List (Option Bool) := simMarkBlock old
  have holdM : oldM.length = e.n := by
    simp [oldM, simMarkBlock_length, hold]
  let T₂ : Tape (Option Bool) :=
    ((Tape.move Dir.right)^[e.n]
      (Tape.mk' L (ListBlank.append oldM R))).write
        (simMarkCell
          ((Tape.move Dir.right)^[e.n]
            (Tape.mk' L (ListBlank.append oldM R))).head)
  let R' : ListBlank (Option Bool) := T₂.right₀
  let Trew : Tape (Option Bool) := (Tape.move Dir.left)^[e.n] T₂
  have hread' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
      ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits), Trew⟩
      (3 * e.n + 2) := by
    simpa [Trew, T₂, oldM] using hread
  have hshape : Trew = Tape.mk' L (ListBlank.append oldM R') := by
    have hT₂ : T₂ = Tape.mk'
        (ListBlank.append oldM.reverse L) R' := by
      calc
        T₂ = Tape.mk' T₂.left T₂.right₀ :=
          (Tape.mk'_left_right₀ T₂).symm
        _ = Tape.mk' (ListBlank.append oldM.reverse L) R' := by
          congr 1
          simp [T₂, ← holdM, tape_move_right_block oldM L R]
    calc
      Trew = (Tape.move Dir.left)^[e.n] T₂ := rfl
      _ = (Tape.move Dir.left)^[e.n]
          (Tape.mk' (ListBlank.append oldM.reverse L) R') := by rw [hT₂]
      _ = Tape.mk' L (ListBlank.append oldM R') := by
        rw [← holdM, tape_move_left_block]
  have hhead : (Tape.mk' L (ListBlank.append oldM R')).head.isSome := by
    rw [Tape.mk'_head]
    cases old with
    | nil => simp at hold; omega
    | cons x xs =>
        have hmem : (ListBlank.append oldM R').head ∈ oldM := by
          simp [oldM, simMarkBlock, ListBlank.append]
        exact simMarkBlock_marked (x :: xs) _ hmem
  have hbits_eq : e.dec bits = a := by
    have hv : bits =
        (⟨old.map (Option.getD · false), by simp [hold]⟩ :
          List.Vector Bool e.n) := by
      apply List.Vector.eq
      exact hbits
    rw [hv]
    exact hdec
  have hzero := simCleanMachine_rewind_zero_halt_step M e q bits
    (Tape.mk' L (ListBlank.append oldM R')) hhead
    (by simpa [hbits_eq] using hm)
  have hzero' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.rewind q ⟨0, Nat.zero_lt_succ _⟩ bits), Trew⟩
      ⟨.run (.done), Trew⟩ 1 := by
    rw [← hshape] at hzero
    exact stepsTo_cons _ hzero (stepsTo_zero _ _)
  have hRtail := simCleanPartialWriteTail_eq e old L R hold
  have hmark : (simMarkCell R.head).isSome := by
    cases R.head <;> simp [simMarkCell]
  have hR' : SimCleanTailOccupied R' := by
    have hR'form : R' = R.tail.cons (simMarkCell R.head) := by
      change simCleanPartialWriteTail e old L R = _
      exact hRtail
    rw [hR'form]
    exact simCleanTailOccupied_append_mark R hR (simMarkCell R.head) hmark
  have hclean := simCleanMachine_marked_halt_cleanup_rep M e .done oldM
    L R' ls holdM (simMarkBlock_marked old) hL hR'
    (by simp [simMachine]) hn
  obtain ⟨out, hclean⟩ := hclean
  have hLmk : ListBlank.mk ls = L := hL.1.symm
  have hclean' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.done), Tape.mk' L (ListBlank.append oldM R')⟩
      ⟨.final, Tape.mk₁ (tapeSymbols out)⟩ (3 * ls.length + 4) := by
    simpa [hLmk] using hclean.1
  have hfirst := stepsTo_trans (t₁ := 3 * e.n + 2) (t₂ := 1) _ hread' hzero'
  rw [hshape] at hfirst
  have htotal := stepsTo_trans (t₁ := 1 + (3 * e.n + 2))
    (t₂ := 3 * ls.length + 4) _ hfirst hclean'
  refine ⟨out, ?_⟩
  have htime : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), Tape.mk' L (ListBlank.append old R)⟩
      ⟨.final, Tape.mk₁ (tapeSymbols out)⟩
      (3 * e.n + 3 * ls.length + 7) := by
    convert htotal using 1
    all_goals omega
  refine ⟨htime, ?_, ?_⟩
  let vM : List.Vector Bool e.n :=
    ⟨(simMarkBlock old).map (Option.getD · false), by
      simpa [oldM] using holdM⟩
  let vO : List.Vector Bool e.n :=
    ⟨old.map (Option.getD · false), by simp [hold]⟩
  have hv : vM = vO := by
    apply Subtype.ext
    simp [vM, vO, simMarkBlock_getD]
  have hdecM : e.dec vM = a := by
    rw [hv]
    exact hdec
  · exact hclean.2.1.trans hdecM
  · exact hclean.2.2


end NPComplete.CookLevin
