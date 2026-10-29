module

public import NPComplete.CookLevin.UniformEmit.CNFEmitLoop

/-!
# Decoder bounds

CNF decoding must fit the store and leave enough output space for the transformed instance. This
module tracks decoded statistics and encoded-size bounds so the producer's layout can be justified
without embedding arithmetic in the emitter.
-/

@[expose] public section

namespace NPComplete.CookLevin

open NPComplete.RAMToTM
open NPComplete.BoundedWhile
  (Program Store Expr eval_seq eval_assign eval_ifNZ eval_forN eval_skip eval_assignInd
    loopEval loopEval_succ writeReg writeReg_diff writeReg_same)
open NPComplete.BitEncoding
  (Bits encodeList encodeNat encodeNat_length encodeList_length_ge)
open NPComplete.SAT (Literal ThreeClause ThreeCNF encodeLiteral)


lemma uniform_save_set_arena_savedBound (σ : Store) (N : ℕ) (h0 : σ 0 = N) :
    let σa := uniformSetArenaProg.eval (uniformSaveBoundProg.eval σ)
    σa uctSavedBoundReg = N ∧ σa 0 = uniformME.eval (uniformSaveBoundProg.eval σ) := by
  have hs := uniformSaveBoundProg_eval σ
  have hne : uctSavedBoundReg ≠ 0 := by decide
  refine ⟨?_, uniformSetArenaProg_eval (uniformSaveBoundProg.eval σ)⟩
  simp [uniformSetArenaProg, eval_assign, writeReg_diff _ 0 _ uctSavedBoundReg hne]
  exact hs.1.trans h0

lemma encodeList_flatten_ge_of_mem {α : Type} (enc : α → Bits) (xs : List α) (x : α)
    (hx : x ∈ xs) : (enc x).length ≤ (xs.map enc).flatten.length := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      rcases List.mem_cons.mp hx with h | h
      · subst h; omega
      · exact Nat.le_add_left_of_le (ih h)

lemma encodeList_length_ge_of_mem {α : Type} (enc : α → Bits) (xs : List α) (x : α)
    (hx : x ∈ xs) : (enc x).length ≤ (encodeList enc xs).length := by
  have hflat := encodeList_flatten_ge_of_mem enc xs x hx
  simp only [encodeList, List.length_append]
  exact Nat.le_add_left_of_le hflat

lemma encodeCNF_eq_lists (φ : CNF) :
    encodeCNF φ =
      encodeList (encodeList encodeLiteral)
        (φ.clauses.map (fun c => c.lits)) := by
  have hmap : φ.clauses.map encodeClause =
      (φ.clauses.map (fun c => c.lits)).map (encodeList encodeLiteral) := by
    simp [encodeClause, List.map_map, Function.comp_def]
  simp [encodeCNF, encodeList, hmap]

lemma encodeCNF_length_ge_clauseCount (φ : CNF) :
    φ.clauses.length + 1 ≤ (encodeCNF φ).length :=
  encodeList_length_ge_count encodeClause φ.clauses

lemma encodeCNF_clause_lits_bound (φ : CNF) (c : Clause) (hc : c ∈ φ.clauses) :
    c.lits.length + 1 ≤ (encodeCNF φ).length :=
  (encodeList_length_ge_count encodeLiteral c.lits).trans
    (encodeList_length_ge_of_mem encodeClause φ.clauses c hc)

lemma encodeCNF_literal_var_bound (φ : CNF) (c : Clause) (hc : c ∈ φ.clauses)
    (l : Literal) (hl : l ∈ c.lits) : l.var + 1 ≤ (encodeCNF φ).length := by
  have hlit : l.var + 1 ≤ (encodeLiteral l).length := by
    cases l <;> simp [encodeLiteral, encodeNat_length, Literal.var]
  exact hlit.trans <|
    (encodeList_length_ge_of_mem encodeLiteral c.lits l hl).trans
      (encodeList_length_ge_of_mem encodeClause φ.clauses c hc)

lemma encodeCNF_scan_bounds (φ : CNF) :
    ∀ ls ∈ φ.clauses.map (fun c : Clause => c.lits),
      ls.length + 1 ≤ (encodeCNF φ).length ∧
        ∀ l ∈ ls, l.var + 1 ≤ (encodeCNF φ).length := by
  intro ls hls
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hls
  exact ⟨encodeCNF_clause_lits_bound φ c hc,
    fun l hl => encodeCNF_literal_var_bound φ c hc l hl⟩

lemma cnfFreshBaseStat_add (base : ℕ) (cs : List (List Literal)) :
    cnfFreshBaseStat base cs = base + cnfFreshBaseStat 0 cs := by
  induction cs generalizing base with
  | nil => simp [cnfFreshBaseStat]
  | cons ls rest ih =>
      simp only [cnfFreshBaseStat, clauseFreshBaseStat_eq_length]
      rw [ih, ih (base := 0 + clauseFreshIncByLength ls.length), Nat.zero_add]
      ac_rfl

lemma uniformPostDecodeStatsProg_eval (σ : Store) (m f s : ℕ)
    (hm : σ uctMaxReg = m) (hf : σ uctFreshReg = f) (hs : σ uctSeenReg = s) :
    (uniformPostDecodeStatsProg.eval σ) uctMaxReg = (if s ≠ 0 then m + 1 else m) ∧
    (uniformPostDecodeStatsProg.eval σ) uctFreshReg =
      (if s ≠ 0 then m + 1 else m) + f ∧
    (uniformPostDecodeStatsProg.eval σ) uctTmpReg = f ∧
    (uniformPostDecodeStatsProg.eval σ) uctSeenReg = s := by
  have htm : uctTmpReg ≠ uctMaxReg := by decide
  have htf : uctTmpReg ≠ uctFreshReg := by decide
  have hts : uctTmpReg ≠ uctSeenReg := by decide
  have hmf : uctMaxReg ≠ uctFreshReg := by decide
  have hms : uctMaxReg ≠ uctSeenReg := by decide
  have hfs : uctFreshReg ≠ uctSeenReg := by decide
  set σ1 := (Program.assign uctTmpReg (.reg uctFreshReg)).eval σ
  have h1m : σ1 uctMaxReg = m := by
    simp [σ1, eval_assign, Expr.eval, hf]
    exact (writeReg_diff σ uctTmpReg f uctMaxReg (Ne.symm htm)).trans hm
  have h1t : σ1 uctTmpReg = f := by
    simp [σ1, eval_assign, Expr.eval, hf, writeReg_same]
  have h1f : σ1 uctFreshReg = f := by
    simp [σ1, eval_assign, Expr.eval, hf]
    exact (writeReg_diff σ uctTmpReg f uctFreshReg (Ne.symm htf)).trans hf
  have h1s : σ1 uctSeenReg = s := by
    simp [σ1, eval_assign, Expr.eval, hf]
    exact (writeReg_diff σ uctTmpReg f uctSeenReg (Ne.symm hts)).trans hs
  have hseq : uniformPostDecodeStatsProg.eval σ =
      (Program.assign uctFreshReg (.add (.reg uctMaxReg) (.reg uctTmpReg))).eval
        ((Program.ifNZ (.reg uctSeenReg)
          (Program.assign uctMaxReg (.add (.reg uctMaxReg) (.const 1)))
          .skip).eval σ1) := by
    simp [uniformPostDecodeStatsProg, eval_seq, σ1]
  rw [hseq]
  by_cases hz : s = 0
  · subst hz
    have hif : (Program.ifNZ (.reg uctSeenReg)
        (Program.assign uctMaxReg (.add (.reg uctMaxReg) (.const 1)))
        .skip).eval σ1 = σ1 := by
      simp [eval_ifNZ, Expr.eval, h1s]
    rw [hif]
    simp [eval_assign, Expr.eval, h1m, h1t, h1s, writeReg_same,
      writeReg_diff σ1 uctFreshReg (m + f) uctMaxReg hmf,
      writeReg_diff σ1 uctFreshReg (m + f) uctTmpReg htf,
      writeReg_diff σ1 uctFreshReg (m + f) uctSeenReg (Ne.symm hfs)]
  · have hif :
        (Program.ifNZ (.reg uctSeenReg)
          (Program.assign uctMaxReg (.add (.reg uctMaxReg) (.const 1)))
          .skip).eval σ1 =
        writeReg σ1 uctMaxReg (m + 1) := by
      simp [eval_ifNZ, eval_assign, Expr.eval, h1s, h1m, hz]
    rw [hif]
    simp [eval_assign, Expr.eval, writeReg_same, hz, h1t, h1s,
      writeReg_diff σ1 uctMaxReg (m + 1) uctTmpReg htm,
      writeReg_diff σ1 uctMaxReg (m + 1) uctSeenReg (Ne.symm hms),
      writeReg_diff (writeReg σ1 uctMaxReg (m + 1)) uctFreshReg (m + 1 + f)
        uctMaxReg hmf,
      writeReg_diff (writeReg σ1 uctMaxReg (m + 1)) uctFreshReg (m + 1 + f)
        uctTmpReg htf,
      writeReg_diff (writeReg σ1 uctMaxReg (m + 1)) uctFreshReg (m + 1 + f)
        uctSeenReg (Ne.symm hfs)]

lemma litsVarBound_of_ne_nil (ls : List Literal) (hne : ls ≠ []) :
    litsVarBound ls = literalVarMax ls + 1 := by
  induction ls with
  | nil => cases hne rfl
  | cons l rest ih =>
      cases rest with
      | nil => simp [litsVarBound, literalVarMax]
      | cons l2 rest =>
          rw [litsVarBound, literalVarMax, ih (List.cons_ne_nil _ _)]
          omega

lemma cnfSeenStat_zero_max (cs : List (List Literal))
    (h : cnfSeenStat 0 cs = 0) :
    cnfLiteralVarMaxStat 0 cs = 0 := by
  induction cs with
  | nil => simp [cnfLiteralVarMaxStat]
  | cons ls rest ih =>
      have hmem := (cnfSeenStat_zero_iff (ls :: rest)).mp h
      have hls : ls.length = 0 := hmem ls (by simp)
      have hrest : cnfSeenStat 0 rest = 0 := by
        simpa [cnfSeenStat, hls] using h
      simp only [cnfLiteralVarMaxStat]
      have hnil : ls = [] := List.eq_nil_of_length_eq_zero hls
      subst hnil
      simpa [literalVarMax] using ih hrest

lemma cnfLiteralVarMaxStat_max (m : ℕ) (cs : List (List Literal)) :
    cnfLiteralVarMaxStat m cs = max m (cnfLiteralVarMaxStat 0 cs) := by
  induction cs generalizing m with
  | nil => simp [cnfLiteralVarMaxStat]
  | cons ls rest ih =>
      simp only [cnfLiteralVarMaxStat]
      rw [ih, ih (m := max 0 (literalVarMax ls))]
      simp [Nat.max_assoc]

lemma clausesVarBound_eq_seen_max (cs : List Clause) :
    clausesVarBound cs =
      if cnfSeenStat 0 (cs.map (fun c => c.lits)) = 0 then 0
      else cnfLiteralVarMaxStat 0 (cs.map (fun c => c.lits)) + 1 := by
  induction cs with
  | nil => simp [clausesVarBound, cnfSeenStat]
  | cons c rest ih =>
      simp only [clausesVarBound, List.map_cons, cnfSeenStat, cnfLiteralVarMaxStat]
      by_cases hls : c.lits.length = 0
      · have hnil : c.lits = [] := List.eq_nil_of_length_eq_zero hls
        simp [hnil, clauseVarBound, litsVarBound, literalVarMax, ih]
      · have hne : c.lits ≠ [] := fun h => hls (by simp [h])
        have hseen : cnfSeenStat 1 (rest.map (fun d => d.lits)) = 1 :=
          cnfSeenStat_one _
        simp [hls, hseen, clauseVarBound, litsVarBound_of_ne_nil _ hne]
        have hmax := cnfLiteralVarMaxStat_max (literalVarMax c.lits)
          (rest.map (fun d => d.lits))
        rw [hmax]
        by_cases hrest : cnfSeenStat 0 (rest.map (fun d => d.lits)) = 0
        · have hmz := cnfSeenStat_zero_max _ hrest
          simp [hrest, hmz, ih]
        · simp [hrest, ih]

lemma cnfVarBound_eq_seen_max (φ : CNF) :
    cnfVarBound φ =
      if cnfSeenStat 0 (φ.clauses.map (fun c => c.lits)) = 0 then 0
      else cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)) + 1 :=
  clausesVarBound_eq_seen_max φ.clauses

lemma decodeCNFProgramAtSeen_uct_encodeCNF_zero_seed (φ : CNF) :
    let bits := encodeCNF φ
    let σ := uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits)))
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ uctMaxReg =
        cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)) ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ uctFreshReg =
        cnfFreshBaseStat 0 (φ.clauses.map (fun c => c.lits)) ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ uctCountReg =
        cnfThreeCountStat (φ.clauses.map (fun c => c.lits)) ∧
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ uctSeenReg =
        cnfSeenStat 0 (φ.clauses.map (fun c => c.lits)) := by
  set bits := encodeCNF φ
  set σ := uniformControlInitProg.eval
    ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
      (uniformRelocateProg.eval (bitInputStore bits)))
  have hs := uniformControlInitProg_after_cursor bits
  have haddr : 25 ≤ uniformAddrNat bits.length :=
    uniformAddrNat_ge_25 _
  have hlists : BitsFrom σ (uniformAddrNat bits.length)
      (encodeList (encodeList encodeLiteral)
        (φ.clauses.map (fun c => c.lits)) ++ ([] : Bits)) := by
    simpa [σ, bits, encodeCNF_eq_lists, List.append_nil] using
      uniformControlInitProg_bitsFrom bits
  have hrem0 : σ uctRemainingReg = 0 := by
    simpa [σ] using
      uniformControlInitProg_zero uctRemainingReg _ (by simp [uctControlRegs])
  have hmax0 : σ uctMaxReg = 0 := by
    simpa [σ] using
      uniformControlInitProg_zero uctMaxReg _ (by simp [uctControlRegs])
  have hfresh0 : σ uctFreshReg = 0 := by
    simpa [σ] using
      uniformControlInitProg_zero uctFreshReg _ (by simp [uctControlRegs])
  have hcount0 : σ uctCountReg = 0 := by
    simpa [σ] using
      uniformControlInitProg_zero uctCountReg _ (by simp [uctControlRegs])
  have hseen0 : σ uctSeenReg = 0 := by
    simpa [σ] using
      uniformControlInitProg_zero uctSeenReg _ (by simp [uctControlRegs])
  obtain ⟨hmax', hfresh', hcount', hseen', _, _, _, _⟩ :=
    decodeCNFProgramAtSeen_uct_append bits.length
      (φ.clauses.map (fun c => c.lits)) ([] : Bits)
      (uniformAddrNat bits.length) 0 0 0 0 σ
      (by simpa using encodeCNF_length_ge_clauseCount φ) haddr hs.2.2.1
      hrem0 hmax0 hfresh0 hcount0 hseen0 hs.1 (encodeCNF_scan_bounds φ) hlists
  exact ⟨hmax', hfresh', by simpa using hcount', hseen'⟩

lemma uniformPostDecodeStatsProg_zero_seed (φ : CNF) :
    let bits := encodeCNF φ
    let σ0 := uniformControlInitProg.eval
      ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
        (uniformRelocateProg.eval (bitInputStore bits)))
    let σd :=
      (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
        uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
        uctBoundReg uctSeenReg).eval σ0
    let σp := uniformPostDecodeStatsProg.eval σd
    σp uctMaxReg = cnfVarBound φ ∧
    σp uctFreshReg =
      cnfVarBound φ + cnfFreshBaseStat 0 (φ.clauses.map (fun c => c.lits)) ∧
    (uniformFreshFromMaxProg.eval σp) uctFreshReg = cnfVarBound φ := by
  obtain ⟨hmax, hfresh, hcount, hseen⟩ :=
    decodeCNFProgramAtSeen_uct_encodeCNF_zero_seed φ
  set bits := encodeCNF φ
  set σ0 := uniformControlInitProg.eval
    ((uniformCursorInitProg uctCursorReg uctInputBaseReg).eval
      (uniformRelocateProg.eval (bitInputStore bits)))
  set σd :=
    (decodeCNFProgramAtSeen uctCursorReg uctPolReg uctVarReg uctDoneReg uctOuterReg
      uctRemainingReg uctMaxReg uctLengthReg uctFreshReg uctCountReg uctTmpReg
      uctBoundReg uctSeenReg).eval σ0
  have hp := uniformPostDecodeStatsProg_eval σd
    (cnfLiteralVarMaxStat 0 (φ.clauses.map (fun c => c.lits)))
    (cnfFreshBaseStat 0 (φ.clauses.map (fun c => c.lits)))
    (cnfSeenStat 0 (φ.clauses.map (fun c => c.lits))) hmax hfresh hseen
  have hbound := cnfVarBound_eq_seen_max φ
  have hmax' : (uniformPostDecodeStatsProg.eval σd) uctMaxReg = cnfVarBound φ := by
    have h := hp.1
    by_cases hz : cnfSeenStat 0 (φ.clauses.map (fun c => c.lits)) = 0
    · have hmz := cnfSeenStat_zero_max _ hz
      simp [hz, hmz] at h hbound
      exact h.trans hbound.symm
    · simp [hz] at h hbound
      exact h.trans hbound.symm
  refine ⟨hmax', ?_, ?_⟩
  · have h := hp.2.1
    by_cases hz : cnfSeenStat 0 (φ.clauses.map (fun c => c.lits)) = 0
    · have hmz := cnfSeenStat_zero_max _ hz
      simp [hz, hmz] at h hbound
      simpa [hbound] using h
    · simp [hz] at h hbound
      simpa [hbound] using h
  · simp [uniformFreshFromMaxProg, eval_assign, Expr.eval, writeReg_same]
    exact hmax'

lemma uniformFreshFromMaxProg_eval (σ : Store) :
    (uniformFreshFromMaxProg.eval σ) uctFreshReg = σ uctMaxReg := by
  simp [uniformFreshFromMaxProg, eval_assign, Expr.eval, writeReg_same]

end NPComplete.CookLevin
