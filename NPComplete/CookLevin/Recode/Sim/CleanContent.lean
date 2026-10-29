module

public import NPComplete.CookLevin.Recode.Sim.CleanStatement

/-!
# Clean-tape content simulation

A symbol-level write or move must preserve block decoding when the tape is
represented by marked bit blocks. This layer proves those local content
relations, keeping tape-data bookkeeping separate from phase-by-phase execution.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_succ stepsTo_cons stepsTo_trans)

lemma simCleanMachine_write_content_nonempty {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s : Γ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (l ys : List Γ) (bl br : List (List (Option Bool)))
    (a y : Γ) (b₂ b : List (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk l)
      (ListBlank.mk (a :: y :: ys)))
    (hU : U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk (b ++ b₂ ++ rawBlocksRight br)))
    (hbl : RawBlocksRel e bl l) (hbr : RawBlocksRel e br ys)
    (hb₂ : BlockDecodes e b₂ y) (hb : BlockDecodes e b a)
    (hblm : BlocksMarked bl)
    (hcontent : BlocksContentMarked (b₂ :: br) (y :: ys))
    (hm : M q T.head = some (q', TM0.Stmt.write s)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.write s)) ∧
      RawTapeCleanContentRel e (T.write s) U' := by
  have hhead : T.head = a := by
    rw [hT]
    rfl
  have hm' : M q a = some (q', TM0.Stmt.write s) := by
    simpa [hhead] using hm
  have hblen : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simp [hblen]⟩ = a :=
    hb.choose_spec
  let L : ListBlank (Option Bool) := ListBlank.mk (rawBlocksLeft bl)
  let R : ListBlank (Option Bool) :=
    ListBlank.mk (b₂ ++ rawBlocksRight br)
  have hU' : U = Tape.mk' L (ListBlank.append b R) := by
    rw [hU]
    simp [L, R]
  obtain ⟨bits, R', hbits, hsteps, hR'eq⟩ :=
    simCleanMachine_partial_write_macro M e q q' s a b L R
      hblen hdec hm' hn
  have hb₂ne : b₂ ≠ [] := by
    intro hnil
    have h := blockDecodes_length hb₂
    simp [hnil] at h
    omega
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb₂ne
  have hb₂' : BlockDecodes e (simMarkCell z :: zs) y := by
    simpa using blockDecodes_mark_head_tail hb₂ hn
  have hnext : y = default ∨ BlockMarked (simMarkCell z :: zs) := by
    simp only [BlocksContentMarked] at hcontent
    rcases hcontent.1 with hy | hmark
    · exact Or.inl hy
    · exact Or.inr (blockMarked_mark_head_tail hmark (by simp))
  have hR' : R' = ListBlank.mk
      (simMarkCell z :: zs ++ rawBlocksRight br) := by
    rw [hR'eq, simCleanPartialWriteTail_eq e b L R hblen]
    simp [R]
  let U' : Tape (Option Bool) :=
    Tape.mk' L (ListBlank.append (rawEncodeBlock e s) R')
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
      (simCleanStmtTime e (.write s)) := by
    rw [hU']
    dsimp [U']
    simpa [simCleanStmtTime, rawEncodeBlock] using hsteps
  refine ⟨U', hsteps', ?_⟩
  refine ⟨l, y :: ys, bl, (simMarkCell z :: zs) :: br, s,
    rawEncodeBlock e s, ?_, ?_, hbl, RawBlocksRel.cons hb₂' hbr,
    rawEncodeBlock_decodes e s, hblm, ?_⟩
  · rw [hT]
    simp [Tape.write_mk']
  · dsimp [U']
    rw [hR']
    simp [L, rawBlocksLeft, rawBlocksRight]
  · simp only [BlocksContentMarked]
    exact ⟨hnext, hcontent.2⟩

lemma simCleanMachine_write_content_blank {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s : Γ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (l : List Γ) (bl : List (List (Option Bool)))
    (a : Γ) (b : List (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk l) (ListBlank.mk [a]))
    (hU : U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk b))
    (hbl : RawBlocksRel e bl l) (hb : BlockDecodes e b a)
    (hblm : BlocksMarked bl)
    (hm : M q T.head = some (q', TM0.Stmt.write s)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.write s)) ∧
      RawTapeCleanContentRel e (T.write s) U' := by
  have hhead : T.head = a := by
    rw [hT]
    rfl
  have hm' : M q a = some (q', TM0.Stmt.write s) := by
    simpa [hhead] using hm
  have hblen : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simp [hblen]⟩ = a :=
    hb.choose_spec
  have hn0 : 0 < e.n := by omega
  let L : ListBlank (Option Bool) := ListBlank.mk (rawBlocksLeft bl)
  let blank : List (Option Bool) := List.replicate e.n none
  let R : ListBlank (Option Bool) := ListBlank.mk blank
  have hU' : U = Tape.mk' L (ListBlank.append b R) := by
    have hblank : ListBlank.mk (b ++ blank) = ListBlank.mk b := by
      apply listBlank_mk_append_all_none
      intro x hx
      simp [blank] at hx
      exact hx.2
    rw [hU]
    dsimp [L, R]
    rw [ListBlank.append_mk]
    rw [hblank]
  obtain ⟨bits, R', hbits, hsteps, hR'eq⟩ :=
    simCleanMachine_partial_write_macro M e q q' s a b L R
      hblen hdec hm' hn0
  let blankMarked : List (Option Bool) :=
    some false :: List.replicate (e.n - 1) none
  have hblankLen : blankMarked.length = e.n := by
    simp [blankMarked]
    omega
  have hblankDec : BlockDecodes e blankMarked (default : Γ) := by
    apply blockDecodes_congr (blockDecodes_default e)
    · simpa only [List.length_replicate] using hblankLen
    · have hen : e.n = (e.n - 1) + 1 := by omega
      rw [hen]
      simp [blankMarked, List.replicate_succ]
  have hR' : R' = ListBlank.mk [some false] :=
    hR'eq.trans (simCleanPartialWriteTail_blank b L hblen hn0)
  let U' : Tape (Option Bool) :=
    Tape.mk' L (ListBlank.append (rawEncodeBlock e s) R')
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
      (simCleanStmtTime e (.write s)) := by
    rw [hU']
    dsimp [U']
    simpa [simCleanStmtTime, rawEncodeBlock] using hsteps
  refine ⟨U', hsteps', ?_⟩
  refine ⟨l, [default], bl, [blankMarked], s, rawEncodeBlock e s,
    ?_, ?_, hbl, RawBlocksRel.cons hblankDec RawBlocksRel.nil,
    rawEncodeBlock_decodes e s, hblm, ?_⟩
  · rw [hT]
    have htail : ListBlank.mk ([s, default] : List Γ) =
        ListBlank.mk [s] := by
      have h := listBlank_mk_append_all_none ([s] : List Γ) [default]
        (by
          intro x hx
          simp at hx
          exact hx)
      simpa using h
    simp [Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk]
    rw [htail]
  · dsimp [U']
    rw [hR']
    have htail : ListBlank.mk
        (rawEncodeBlock e s ++ blankMarked) =
        ListBlank.mk (rawEncodeBlock e s ++ [some false]) := by
      dsimp [blankMarked]
      have h := listBlank_mk_append_all_none
        (rawEncodeBlock e s ++ [some false])
        (List.replicate (e.n - 1) none) (by
          intro x hx
          simp at hx
          exact hx.2)
      simpa [List.append_assoc] using h
    rw [ListBlank.append_mk]
    simp only [rawBlocksRight, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [htail]
  · simp only [BlocksContentMarked]
    simp

lemma simCleanMachine_move_right_content_nonempty {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (l ys : List Γ) (bl br : List (List (Option Bool)))
    (a y : Γ) (b₂ b : List (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk l)
      (ListBlank.mk (a :: y :: ys)))
    (hU : U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk (b ++ b₂ ++ rawBlocksRight br)))
    (hbl : RawBlocksRel e bl l) (hbr : RawBlocksRel e br ys)
    (hb₂ : BlockDecodes e b₂ y) (hb : BlockDecodes e b a)
    (hblm : BlocksMarked bl)
    (hcontent : BlocksContentMarked (b₂ :: br) (y :: ys))
    (hm : M q T.head = some (q', TM0.Stmt.move Dir.right)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.move Dir.right)) ∧
      RawTapeCleanContentRel e (T.move Dir.right) U' := by
  have hhead : T.head = a := by
    rw [hT]
    rfl
  have hm' : M q a = some (q', TM0.Stmt.move Dir.right) := by
    simpa [hhead] using hm
  have hblen : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simp [hblen]⟩ = a :=
    hb.choose_spec
  let L : ListBlank (Option Bool) := ListBlank.mk (rawBlocksLeft bl)
  let R : ListBlank (Option Bool) :=
    ListBlank.mk (b₂ ++ rawBlocksRight br)
  have hU' : U = Tape.mk' L (ListBlank.append b R) := by
    rw [hU]
    simp [L, R]
  obtain ⟨bits, U', hbits, hsteps, htarget⟩ :=
    simCleanMachine_partial_move_macro M e q q' a b L R
      Dir.right hblen hdec hm' hn
  have hb₂len : b₂.length = e.n := blockDecodes_length hb₂
  have hb₂ne : b₂ ≠ [] := by
    intro hnil
    simp [hnil] at hb₂len
    omega
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hb₂ne
  have hb₂' : BlockDecodes e (simMarkCell z :: zs) y := by
    simpa using blockDecodes_mark_head_tail hb₂ hn
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
      (simCleanStmtTime e (.move Dir.right)) := by
    simpa [hU', simCleanStmtTime, L, R]
      using hsteps
  refine ⟨U', hsteps', ?_⟩
  refine ⟨a :: l, ys, simMarkBlock b :: bl, br, y,
    simMarkCell z :: zs, ?_, ?_, ?_, hbr, hb₂',
    blocksMarked_cons.mpr ⟨simMarkBlock_marked b, hblm⟩, ?_⟩
  · rw [hT]
    simp [Tape.move, Tape.mk']
  · rw [htarget]
    rw [simCleanPartialMoveTarget_right_eq e b L R hblen]
    rw [simCleanPartialWriteTail_eq e b L R hblen]
    simp [L, R, rawBlocksLeft, rawBlocksRight]
  · exact RawBlocksRel.cons (blockDecodes_mark hb) hbl
  · exact hcontent.2

lemma simCleanMachine_move_right_content_blank {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (l : List Γ) (bl : List (List (Option Bool)))
    (a : Γ) (b : List (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk l) (ListBlank.mk [a]))
    (hU : U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
      (ListBlank.mk b))
    (hbl : RawBlocksRel e bl l) (hb : BlockDecodes e b a)
    (hblm : BlocksMarked bl)
    (hm : M q T.head = some (q', TM0.Stmt.move Dir.right)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.move Dir.right)) ∧
      RawTapeCleanContentRel e (T.move Dir.right) U' := by
  have hhead : T.head = a := by
    rw [hT]
    rfl
  have hm' : M q a = some (q', TM0.Stmt.move Dir.right) := by
    simpa [hhead] using hm
  have hblen : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simp [hblen]⟩ = a :=
    hb.choose_spec
  let L : ListBlank (Option Bool) := ListBlank.mk (rawBlocksLeft bl)
  let blank : List (Option Bool) := List.replicate e.n none
  let R : ListBlank (Option Bool) := ListBlank.mk blank
  have hU' : U = Tape.mk' L (ListBlank.append b R) := by
    have hblank : ListBlank.mk (b ++ blank) = ListBlank.mk b := by
      apply listBlank_mk_append_all_none
      intro x hx
      simp [blank] at hx
      exact hx.2
    rw [hU]
    dsimp [L, R]
    rw [ListBlank.append_mk, hblank]
  obtain ⟨bits, U', hbits, hsteps, htarget⟩ :=
    simCleanMachine_partial_move_macro M e q q' a b L R
      Dir.right hblen hdec hm' hn
  have htail : simCleanPartialWriteTail e b L R =
      ListBlank.mk [some false] :=
    simCleanPartialWriteTail_blank b L hblen hn
  let blankMarked : List (Option Bool) :=
    some false :: List.replicate (e.n - 1) none
  have hblankLen : blankMarked.length = e.n := by
    dsimp [blankMarked]
    simp only [List.length_replicate]
    simpa [Nat.add_comm] using
      (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hn))
  have hblankDec : BlockDecodes e blankMarked (default : Γ) := by
    apply blockDecodes_congr (blockDecodes_default e)
    · simpa only [List.length_replicate] using hblankLen
    · have hen : e.n = (e.n - 1) + 1 := by omega
      rw [hen]
      simp [blankMarked, List.replicate_succ]
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
      (simCleanStmtTime e (.move Dir.right)) := by
    simpa [hU', simCleanStmtTime, L, R]
      using hsteps
  refine ⟨U', hsteps', ?_⟩
  refine ⟨a :: l, [], simMarkBlock b :: bl, [], default, blankMarked,
    ?_, ?_, RawBlocksRel.cons (blockDecodes_mark hb) hbl,
    RawBlocksRel.nil, hblankDec,
    blocksMarked_cons.mpr ⟨simMarkBlock_marked b, hblm⟩,
    by simp [BlocksContentMarked]⟩
  · rw [hT]
    simp [Tape.move, Tape.mk']
  · rw [htarget, simCleanPartialMoveTarget_right_eq e b L R hblen, htail]
    have hblankEq : ListBlank.mk blankMarked = ListBlank.mk [some false] := by
      dsimp [blankMarked]
      have h := listBlank_mk_append_all_none
        ([some false] : List (Option Bool))
        (List.replicate (e.n - 1) none) (by
          intro x hx
          simp at hx
          exact hx.2)
      simpa using h
    simp only [rawBlocksRight, List.flatten_nil, List.append_nil]
    rw [hblankEq]
    simp [L, rawBlocksLeft]

lemma simCleanMachine_move_left_content_nonempty {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (xs r : List Γ) (bl br : List (List (Option Bool)))
    (x a y : Γ) (b₀ b₂ b : List (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk (x :: xs))
      (ListBlank.mk (a :: y :: r)))
    (hU : U = Tape.mk'
      (ListBlank.mk (rawBlocksLeft (b₀ :: bl)))
      (ListBlank.mk (b ++ b₂ ++ rawBlocksRight br)))
    (hbl : RawBlocksRel e bl xs) (hbr : RawBlocksRel e br r)
    (hb₀ : BlockDecodes e b₀ x) (hb₂ : BlockDecodes e b₂ y)
    (hb : BlockDecodes e b a) (hblm : BlocksMarked bl)
    (hcontent : BlocksContentMarked (b₂ :: br) (y :: r))
    (hm : M q T.head = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.move Dir.left)) ∧
      RawTapeCleanContentRel e (T.move Dir.left) U' := by
  have hhead : T.head = a := by
    rw [hT]
    rfl
  have hm' : M q a = some (q', TM0.Stmt.move Dir.left) := by
    simpa [hhead] using hm
  have hblen : b.length = e.n := blockDecodes_length hb
  have hdec : e.dec ⟨b.map (Option.getD · false), by simp [hblen]⟩ = a :=
    hb.choose_spec
  have hb₀len : b₀.length = e.n := blockDecodes_length hb₀
  have hb₂len : b₂.length = e.n := blockDecodes_length hb₂
  have hb₀ne : b₀ ≠ [] := by
    intro hnil
    simp [hnil] at hb₀len
    omega
  have hb₂ne : b₂ ≠ [] := by
    intro hnil
    simp [hnil] at hb₂len
    omega
  let L₀ : ListBlank (Option Bool) := ListBlank.mk (rawBlocksLeft bl)
  let L : ListBlank (Option Bool) := ListBlank.append b₀.reverse L₀
  let R : ListBlank (Option Bool) :=
    ListBlank.mk (b₂ ++ rawBlocksRight br)
  have hU' : U = Tape.mk' L (ListBlank.append b R) := by
    rw [hU]
    simp [L, L₀, R, rawBlocksLeft, rawBlocksRight]
  obtain ⟨bits, U', hbits, hsteps, htarget⟩ :=
    simCleanMachine_partial_move_macro M e q q' a b L R
      Dir.left hblen hdec hm' hn
  obtain ⟨z₀, zs₀, rfl⟩ := List.exists_cons_of_ne_nil hb₀ne
  obtain ⟨z₂, zs₂, rfl⟩ := List.exists_cons_of_ne_nil hb₂ne
  have hbcur : BlockDecodes e (simMarkCell z₀ :: zs₀) x := by
    simpa using blockDecodes_mark_head_tail hb₀ hn
  have hb₂' : BlockDecodes e (simMarkCell z₂ :: zs₂) y := by
    simpa using blockDecodes_mark_head_tail hb₂ hn
  have hnext : y = default ∨ BlockMarked (simMarkCell z₂ :: zs₂) := by
    simp only [BlocksContentMarked] at hcontent
    rcases hcontent.1 with hy | hmark
    · exact Or.inl hy
    · exact Or.inr (blockMarked_mark_head_tail hmark (by simp))
  have htail : simCleanPartialWriteTail e b L R =
      ListBlank.mk (simMarkCell z₂ :: zs₂ ++ rawBlocksRight br) := by
    rw [simCleanPartialWriteTail_eq e b L R hblen]
    simp [R]
  have hsteps' : StepsTo (TM0.step (simCleanMachine M e))
      ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
      (simCleanStmtTime e (.move Dir.left)) := by
    simpa [hU', simCleanStmtTime, L, L₀, R]
      using hsteps
  refine ⟨U', hsteps', ?_⟩
  refine ⟨xs, a :: y :: r, bl,
    simMarkBlock b :: (simMarkCell z₂ :: zs₂) :: br, x,
    simMarkCell z₀ :: zs₀, ?_, ?_, hbl,
    RawBlocksRel.cons (blockDecodes_mark hb) (RawBlocksRel.cons hb₂' hbr),
    hbcur, hblm, ?_⟩
  · rw [hT]
    simp [Tape.move, Tape.mk']
  · rw [htarget]
    rw [simCleanPartialMoveTarget_left_eq e b L₀ (z₀ :: zs₀) L R
      (by simpa using hb₀len) (by rfl) hblen hn]
    rw [htail]
    simp [L₀, rawBlocksLeft, rawBlocksRight]
  · simp only [BlocksContentMarked]
    refine ⟨Or.inr (simMarkBlock_marked b), ?_⟩
    exact ⟨hnext, hcontent.2⟩

/-- Write case of the clean content step, dispatching on whether a next block exists. -/
lemma simCleanMachine_normal_stmt_step_content_write {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (z : Γ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (hrel : RawTapeCleanContentRel e T U)
    (hm : M q T.head = some (q', TM0.Stmt.write z)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.write z)) ∧
      RawTapeCleanContentRel e (T.write z) U' := by
  rcases hrel with ⟨l, r, bl, br, a, b, hT, hU,
    hbl, hbr, hb, hblm, hcontent⟩
  cases hbr with
  | nil =>
      have hU' : U = Tape.mk'
          (ListBlank.mk (rawBlocksLeft bl)) (ListBlank.mk b) := by
        simpa [rawBlocksRight] using hU
      exact simCleanMachine_write_content_blank M e q q' z T U l bl a b
        hT hU' hbl hb hblm hm hn
  | @cons b₂ y br' ys hb₂ hbr' =>
      have hU' : U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
          (ListBlank.mk (b ++ b₂ ++ rawBlocksRight br')) := by
        simpa [rawBlocksRight, List.append_assoc] using hU
      exact simCleanMachine_write_content_nonempty M e q q' z T U
        l ys bl br' a y b₂ b hT hU' hbl hbr' hb₂ hb
        hblm hcontent hm hn

/-- Right-move case of the clean content step, dispatching on whether a next block exists. -/
lemma simCleanMachine_normal_stmt_step_content_move_right {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (hrel : RawTapeCleanContentRel e T U)
    (hm : M q T.head = some (q', TM0.Stmt.move Dir.right)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.move Dir.right)) ∧
      RawTapeCleanContentRel e (T.move Dir.right) U' := by
  rcases hrel with ⟨l, r, bl, br, a, b, hT, hU,
    hbl, hbr, hb, hblm, hcontent⟩
  cases hbr with
  | nil =>
      have hU' : U = Tape.mk'
          (ListBlank.mk (rawBlocksLeft bl)) (ListBlank.mk b) := by
        simpa [rawBlocksRight] using hU
      exact simCleanMachine_move_right_content_blank M e q q' T U l bl
        a b hT hU' hbl hb hblm hm hn
  | @cons b₂ y br' ys hb₂ hbr' =>
      have hU' : U = Tape.mk' (ListBlank.mk (rawBlocksLeft bl))
          (ListBlank.mk (b ++ b₂ ++ rawBlocksRight br')) := by
        simpa [rawBlocksRight, List.append_assoc] using hU
      exact simCleanMachine_move_right_content_nonempty M e q q' T U
        l ys bl br' a y b₂ b hT hU' hbl hbr' hb₂ hb
        hblm hcontent hm hn

/-- Left move when a left block exists; pads the right side with a blank block if needed. -/
lemma simCleanMachine_normal_stmt_step_content_left_cons {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (xs r : List Γ) (bl br : List (List (Option Bool)))
    (x a : Γ) (b₀ b : List (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk (x :: xs)) (ListBlank.mk (a :: r)))
    (hU : U = Tape.mk' (ListBlank.mk (rawBlocksLeft (b₀ :: bl)))
      (ListBlank.mk (b ++ rawBlocksRight br)))
    (hbl : RawBlocksRel e bl xs) (hbr : RawBlocksRel e br r)
    (hb₀ : BlockDecodes e b₀ x) (hb : BlockDecodes e b a)
    (hblm : BlocksMarked bl) (hcontent : BlocksContentMarked br r)
    (hm : M q T.head = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.move Dir.left)) ∧
      RawTapeCleanContentRel e (T.move Dir.left) U' := by
  cases hbr with
  | nil =>
      let blank : List (Option Bool) := List.replicate e.n none
      have hblank : BlockDecodes e blank (default : Γ) := by
        simpa [blank] using blockDecodes_default e
      have hT' : T = Tape.mk' (ListBlank.mk (x :: xs))
          (ListBlank.mk (a :: default :: [])) := by
        rw [hT]
        have hr : ListBlank.mk [a] = ListBlank.mk (a :: default :: []) := by
          simpa using (listBlank_mk_append_default [a]).symm
        rw [hr]
      have hright : ListBlank.mk (b ++ blank) = ListBlank.mk b := by
        apply listBlank_mk_append_all_none
        intro v hv
        simp [blank] at hv
        exact hv.2
      have hU' : U = Tape.mk' (ListBlank.mk (rawBlocksLeft (b₀ :: bl)))
          (ListBlank.mk (b ++ blank)) := by
        rw [hU]
        simp only [rawBlocksRight, List.flatten_nil, List.append_nil]
        rw [hright]
      have hcontent' : BlocksContentMarked [blank] [(default : Γ)] := by
        simp [BlocksContentMarked]
      exact simCleanMachine_move_left_content_nonempty M e q q'
        T U xs [] bl [] x a default b₀ blank b hT'
        (by simpa [rawBlocksRight] using hU') hbl RawBlocksRel.nil hb₀ hblank hb
        hblm hcontent' hm hn
  | @cons b₂ y br' ys hb₂ hbr' =>
      have hU' : U = Tape.mk' (ListBlank.mk (rawBlocksLeft (b₀ :: bl)))
          (ListBlank.mk (b ++ b₂ ++ rawBlocksRight br')) := by
        simpa [rawBlocksRight, List.append_assoc] using hU
      exact simCleanMachine_move_left_content_nonempty M e q q'
        T U xs ys bl br' x a y b₀ b₂ b hT hU'
        hbl hbr' hb₀ hb₂ hb hblm hcontent hm hn

/-- Left move at the left edge; pads the left side with a blank block and reduces to
the case with a left block. -/
lemma simCleanMachine_normal_stmt_step_content_left_nil {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (r : List Γ) (br : List (List (Option Bool)))
    (a : Γ) (b : List (Option Bool))
    (hT : T = Tape.mk' (ListBlank.mk []) (ListBlank.mk (a :: r)))
    (hU : U = Tape.mk' (ListBlank.mk (rawBlocksLeft []))
      (ListBlank.mk (b ++ rawBlocksRight br)))
    (hbr : RawBlocksRel e br r) (hb : BlockDecodes e b a)
    (hcontent : BlocksContentMarked br r)
    (hm : M q T.head = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.move Dir.left)) ∧
      RawTapeCleanContentRel e (T.move Dir.left) U' := by
  let blank : List (Option Bool) := List.replicate e.n none
  have hblank : BlockDecodes e blank (default : Γ) := by
    simpa [blank] using blockDecodes_default e
  have hleft : ListBlank.mk (rawBlocksLeft [blank]) = ListBlank.mk [] := by
    rw [show rawBlocksLeft [blank] = blank by
      simp [rawBlocksLeft, blank, List.reverse_replicate]]
    exact listBlank_mk_replicate_none e.n
  have hT' : T = Tape.mk' (ListBlank.mk [default]) (ListBlank.mk (a :: r)) := by
    rw [hT]
    have hl : ListBlank.mk ([] : List Γ) = ListBlank.mk [default] :=
      (listBlank_mk_append_default ([] : List Γ)).symm
    rw [hl]
  have hU' : U = Tape.mk' (ListBlank.mk (rawBlocksLeft [blank]))
      (ListBlank.mk (b ++ rawBlocksRight br)) := by
    rw [hU, hleft]
    simp [rawBlocksLeft]
  exact simCleanMachine_normal_stmt_step_content_left_cons M e q q' T U []
    r [] br default a blank b hT' hU' RawBlocksRel.nil hbr hblank hb
    blocksMarked_nil hcontent hm hn

/-- Left-move case of the clean content step, dispatching on whether a left block exists. -/
lemma simCleanMachine_normal_stmt_step_content_move_left {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (hrel : RawTapeCleanContentRel e T U)
    (hm : M q T.head = some (q', TM0.Stmt.move Dir.left)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e (.move Dir.left)) ∧
      RawTapeCleanContentRel e (T.move Dir.left) U' := by
  rcases hrel with ⟨l, r, bl, br, a, b, hT, hU,
    hbl, hbr, hb, hblm, hcontent⟩
  cases hbl with
  | nil =>
      exact simCleanMachine_normal_stmt_step_content_left_nil M e q q' T U r br
        a b hT hU hbr hb hcontent hm hn
  | @cons b₀ x bl' xs hb₀ hbl' =>
      exact simCleanMachine_normal_stmt_step_content_left_cons M e q q' T U xs r
        bl' br x a b₀ b hT hU hbl' hbr hb₀ hb
        (blocksMarked_cons.mp hblm).2 hcontent hm hn

lemma simCleanMachine_normal_stmt_step_content {Γ Λ : Type} [Inhabited Γ]
    [Finite Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (e : BlockEnc Γ)
    (q q' : Λ) (s : TM0.Stmt Γ)
    (T : Tape Γ) (U : Tape (Option Bool))
    (hrel : RawTapeCleanContentRel e T U)
    (hm : M q T.head = some (q', s)) (hn : 0 < e.n) :
    ∃ U',
      StepsTo (TM0.step (simCleanMachine M e))
        ⟨.run (.ready q), U⟩ ⟨.run (.ready q'), U'⟩
        (simCleanStmtTime e s) ∧
      RawTapeCleanContentRel e
        (match s with
        | .write a => T.write a
        | .move d => T.move d) U' := by
  cases s with
  | write z => exact simCleanMachine_normal_stmt_step_content_write M e q q' z T U hrel hm hn
  | move d =>
      cases d with
      | right => exact simCleanMachine_normal_stmt_step_content_move_right M e q q' T U hrel hm hn
      | left => exact simCleanMachine_normal_stmt_step_content_move_left M e q q' T U hrel hm hn


end NPComplete.CookLevin
