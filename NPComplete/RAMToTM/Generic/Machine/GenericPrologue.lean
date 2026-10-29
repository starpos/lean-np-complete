module

public import NPComplete.RAMToTM.Generic.Machine.GenericProgramMachine
public import NPComplete.RAMToTM.Generic.Api.BoundedWhileDecider

/-!
# Prologue: loading raw input bits into the RAM's initial memory write-log

`Represents` (`GenericProgramMachine.lean`) states the simulation invariant from the point the
compiled program is *already mid-execution*; it says nothing about how the machine gets from a
raw `Bits` input sitting on `Kg.io` to that first represented state. `compiledInputRAM`
(`BoundedWhileDecider.lean`) fixes what the RAM side of that boundary must be:
`bitInputStore bits`, i.e. cell `0` holds `bits.length`, cell `i+1` holds bit `i`. This file's
job is the other side — realizing that loader as a `Turing.TM2.Stmt` tree that scans `Kg.io` and
builds the corresponding write-log on `Kg.mem` — starting with the target write-log in its
literal push-order form (`inputLogRev`) and proving it denotes exactly `bitInputStore`
(`lookupD_inputLogRev`). The construction separates pure log semantics, the scanning `Stmt` tree,
and cleanup.
-/

@[expose] public section

namespace NPComplete.RAMToTM

open NPComplete.BitEncoding (Bits)

/-- `lookupD` only ever inspects the first matching address in a log, so a prefix with no entry
    at `a` can be dropped for free — the boundary fact `bitLogRev`'s own scan-loop realization
    will need every time a fresh entry is prepended ahead of an untouched suffix. -/
lemma lookupD_append_of_not_mem (l1 l2 : WriteLog) (a d : ℕ) (h : ∀ p ∈ l1, p.1 ≠ a) :
    lookupD (l1 ++ l2) a d = lookupD l2 a d := by
  induction l1 with
  | nil => simp
  | cons p l1' ih =>
    have hp : p.1 ≠ a := h p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ l1', q.1 ≠ a := fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [List.cons_append, lookupD, List.find?, hp]
    exact ih hrest

/-- `lookupD` at any address `a` reduces to searching `l1` alone when nothing in `l2` matches
    `a`: the mirror image of `lookupD_append_of_not_mem` (which drops the *first* operand),
    needed when the fresh entry sits at the *end* of the searched list (a scanning realization
    that grows its log by appending each new write onto whatever is already accumulated, rather
    than prepending). -/
lemma lookupD_append_of_not_mem_snd (l1 l2 : WriteLog) (a d : ℕ) (h : ∀ p ∈ l2, p.1 ≠ a) :
    lookupD (l1 ++ l2) a d = lookupD l1 a d := by
  induction l1 with
  | nil =>
    have hnone : l2.find? (fun e => e.1 = a) = none := by
      induction l2 with
      | nil => rfl
      | cons q l2' ih =>
        simp only [List.find?_cons]
        have hq : ¬ q.1 = a := h q (List.mem_cons_self ..)
        simp [hq, ih (fun r hr => h r (List.mem_cons_of_mem _ hr))]
    simp [lookupD, hnone]
  | cons p l1' ih =>
    simp only [List.cons_append, lookupD, List.find?]
    by_cases hp2 : p.1 = a
    · simp [hp2]
    · simp only [hp2, decide_false]
      exact ih

/-- Per-bit write-log entries for a scanned input, built in the order a scanning prologue
    realization actually leaves them on `Kg.mem` — since `push` always prepends and
    later-consumed bits are pushed later, they end up closer to the stack top, so the TM-level
    scan loop's aggregate effect (`Generic.prologue_scanInput_run`) needs this build order to
    state precisely. -/
def bitLogRev : List Bool → ℕ → WriteLog
  | [], _ => []
  | b :: rest, base => bitLogRev rest (base + 1) ++ (if b then [(base + 1, 1)] else [])

/-- Every entry `bitLogRev` produces for bits `base, base+1, ...` has an address strictly inside
    `(base, base + bits.length]` — needed to show a *later* bit's own entry can never shadow an
    *earlier* one's address when they are combined by appending (the order `bitLogRev`'s own
    recursion builds them in). -/
lemma bitLogRev_mem_range (bits : List Bool) (base : ℕ) :
    ∀ p ∈ bitLogRev bits base, base < p.1 ∧ p.1 ≤ base + bits.length := by
  induction bits generalizing base with
  | nil => simp [bitLogRev]
  | cons b rest ih =>
    intro p hp
    rw [bitLogRev, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨h1, h2⟩ := ih (base + 1) p hp
      refine ⟨by omega, ?_⟩
      simp only [List.length_cons]; omega
    · cases b with
      | false => simp at hp
      | true =>
        simp only [ite_true, List.mem_singleton] at hp
        subst hp
        simp only [List.length_cons]
        omega

/-- `bitLogRev`'s own lookup formula: an entry exists only for addresses strictly inside
    `(base, base + bits.length]` (`bitLogRev_mem_range`), and its value there is exactly the
    corresponding bit. Proved directly by induction on the recursive definition rather than via a
    generic reordering lemma, since the two constituent lists at each step sit on *opposite* sides
    of the `++` (append vs. prepend), not merely permuted within one fixed list. -/
lemma lookupD_bitLogRev (bits : List Bool) (base a : ℕ) :
    lookupD (bitLogRev bits base) a 0 =
      if base < a ∧ a ≤ base + bits.length then
        (if bits.getD (a - base - 1) false then 1 else 0)
      else 0 := by
  induction bits generalizing base with
  | nil => simp [bitLogRev, lookupD]
  | cons b rest ih =>
    rw [bitLogRev]
    by_cases ha : a = base + 1
    · subst ha
      have hnomem : ∀ p ∈ bitLogRev rest (base + 1), p.1 ≠ base + 1 := by
        intro p hp
        have := (bitLogRev_mem_range rest (base + 1) p hp).1
        omega
      cases b with
      | false => simpa using ih (base + 1)
      | true =>
        rw [lookupD_append_of_not_mem _ _ _ _ hnomem]
        simp [lookupD]
    · have hb1 : ∀ p ∈ (if b then [(base + 1, 1)] else ([] : WriteLog)), p.1 ≠ a := by
        intro p hp
        cases b with
        | false => simp at hp
        | true =>
          simp only [ite_true, List.mem_singleton] at hp
          subst hp
          exact fun h => ha h.symm
      rw [lookupD_append_of_not_mem_snd _ _ _ _ hb1, ih (base + 1)]
      by_cases hlt : base + 1 < a
      · have hcond1 : base < a ∧ a ≤ base + (b :: rest).length ↔
            base + 1 < a ∧ a ≤ (base + 1) + rest.length := by
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨by omega, by simp only [List.length_cons] at h2 ⊢; omega⟩
          · rintro ⟨h1, h2⟩
            refine ⟨by omega, by simp only [List.length_cons]; omega⟩
        by_cases hcond : base + 1 < a ∧ a ≤ (base + 1) + rest.length
        · have hcond' := hcond1.mpr hcond
          simp only [hcond, hcond']
          have hidx : a - base - 1 = (a - (base + 1) - 1) + 1 := by omega
          rw [hidx, List.getD_cons_succ]
        · have hcond' : ¬ (base < a ∧ a ≤ base + (b :: rest).length) := by
            rw [hcond1]; exact hcond
          rw [ite_eq_right hcond, ite_eq_right hcond']
      · have h1 : ¬ (base < a) := by omega
        have h2 : ¬ (base + 1 < a) := hlt
        simp [h1, h2]

/-- The write-log a fully-scanned prologue *literally* leaves on `Kg.mem`: `bits.length` at
    address `0`, then `bitLogRev`'s per-bit entries. -/
def inputLogRev (bits : Bits) : WriteLog := (0, bits.length) :: bitLogRev bits 0

/-- `inputLogRev bits` denotes exactly `bitInputStore bits` — the semantic half of the
    `Represents` contract the prologue's literal `Kg.mem` result (`Generic.prologue_run`) must
    satisfy against this witness log. -/
lemma lookupD_inputLogRev (bits : Bits) (a : ℕ) :
    lookupD (inputLogRev bits) a 0 = bitInputStore bits a := by
  unfold inputLogRev bitInputStore
  cases a with
  | zero => simp [lookupD, List.find?]
  | succ r =>
    have h0 : ¬ ((0, bits.length) : ℕ × ℕ).1 = r + 1 := by simp
    simp only [lookupD, List.find?, h0]
    show lookupD (bitLogRev bits 0) (r + 1) 0 = _
    rw [lookupD_bitLogRev]
    by_cases hr : r < bits.length
    · simp [hr]
    · simp [hr]


open NPComplete.BitCostRAM in
/-- `bitLogRev` never produces more entries than there are bits (at most one per bit,
    dropped for `false`). -/
lemma bitLogRev_length_le (bits : List Bool) (base : ℕ) :
    (bitLogRev bits base).length ≤ bits.length := by
  induction bits generalizing base with
  | nil => simp [bitLogRev]
  | cons b rest ih =>
      simp only [bitLogRev, List.length_append, List.length_cons]
      rcases b with _ | _ <;> simp <;> have := ih (base + 1) <;> omega

open NPComplete.BitCostRAM in
/-- Every entry `bitLogRev` produces carries the fixed value `1` (`bitLogRev`'s own
    `(base + 1, 1)` literal). -/
lemma bitLogRev_snd_eq_one (bits : List Bool) (base : ℕ) :
    ∀ p ∈ bitLogRev bits base, p.2 = 1 := by
  induction bits generalizing base with
  | nil => simp [bitLogRev]
  | cons b rest ih =>
      intro p hp
      rw [bitLogRev, List.mem_append] at hp
      rcases hp with hp | hp
      · exact ih (base + 1) p hp
      · cases b with
        | false => simp at hp
        | true => simp only [ite_true, List.mem_singleton] at hp; rw [hp]

open NPComplete.BitCostRAM in
/-- Serializing a write-log costs `O(entries * bitLen B)` once every entry's address/value is
    bounded by `B` — the potential `programImmediatesLe_compile`'s sibling for the prologue's
    memory footprint. This supports bounding prologue/cleanup steps by input length, separately
    from `Δcost`. -/
lemma encodeLog_length_le (log : WriteLog) (B : ℕ) (h : ∀ e ∈ log, e.1 ≤ B ∧ e.2 ≤ B) :
    (encodeLog log).length ≤ log.length * (2 * bitLen B + 2) := by
  induction log with
  | nil => simp [encodeLog]
  | cons e rest ih =>
      obtain ⟨h1, h2⟩ := h e List.mem_cons_self
      have hrest : (encodeLog rest).length ≤ rest.length * (2 * bitLen B + 2) :=
        ih (fun e' he' => h e' (List.mem_cons_of_mem e he'))
      have hentry : (encodeEntry e.1 e.2).length ≤ 2 * bitLen B + 2 := by
        simp only [encodeEntry, List.length_append, List.length_cons, List.length_nil,
          List.length_map, List.length_reverse]
        have hb1 : (natToDigits e.1).length ≤ bitLen B :=
          le_trans (natToDigits_length_le_bitLen e.1) (bitLen_le_of_le h1)
        have hb2 : (natToDigits e.2).length ≤ bitLen B :=
          le_trans (natToDigits_length_le_bitLen e.2) (bitLen_le_of_le h2)
        omega
      simp only [encodeLog, List.map_cons, List.flatten_cons, List.length_append,
        List.length_cons]
      show (encodeEntry e.1 e.2).length + (encodeLog rest).length ≤ (rest.length + 1) * _
      have heq : (rest.length + 1) * (2 * bitLen B + 2) =
          (2 * bitLen B + 2) + rest.length * (2 * bitLen B + 2) := by ring
      omega

lemma inputLogRev_length_le (bits : Bits) : (inputLogRev bits).length ≤ bits.length + 1 := by
  simp only [inputLogRev, List.length_cons]
  have := bitLogRev_length_le bits 0
  omega

lemma inputLogRev_bound (bits : Bits) :
    ∀ e ∈ inputLogRev bits, e.1 ≤ bits.length ∧ e.2 ≤ bits.length := by
  intro e he
  simp only [inputLogRev, List.mem_cons] at he
  rcases he with he | he
  · subst he; exact ⟨by simp, le_refl _⟩
  · obtain ⟨h1, h2⟩ := bitLogRev_mem_range bits 0 e he
    have hlen : 1 ≤ bits.length := by
      rcases bits with _ | ⟨b, rest⟩
      · simp [bitLogRev] at he
      · simp
    exact ⟨by omega, by rw [bitLogRev_snd_eq_one bits 0 e he]; exact hlen⟩

open NPComplete.BitCostRAM in
/-- The prologue's write-log serializes to `O(n log n)` `MemSym`s (`n := bits.length`) — the
    input-length potential used to bound prologue/cleanup step counts, separately from the compiled
    RAM's own `Δcost`. -/
lemma encodeLog_inputLogRev_length_le (bits : Bits) :
    (encodeLog (inputLogRev bits)).length ≤ (bits.length + 1) * (2 * bitLen bits.length + 2) :=
  le_trans (encodeLog_length_le _ _ (inputLogRev_bound bits))
    (Nat.mul_le_mul_right _ (inputLogRev_length_le bits))

/-- Once `addRaw`'s carry has resolved (`false`) against an empty second operand, every
    remaining digit of the first operand is copied through completely unchanged — the pure
    counterpart of `prologueProg`'s `incCopyRest` phase, which the increment aggregation lemma
    (`GenericProgramMachine.lean`'s `Generic` namespace) identifies with it. -/
lemma addRaw_nil_false (l : List Digit) : addRaw l [] false = l := by
  induction l with
  | nil => simp [addRaw]
  | cons d rest ih =>
    have hcond : ¬ (d :: rest = [] ∧ ([] : List Digit) = [] ∧ (false : Bool) = false) := by simp
    have hdc : addDigits ((d :: rest).headD 0) (([] : List Digit).headD 0) false = (d, false) := by
      have hd := d.isLt
      simp only [addDigits, List.headD_cons, List.headD_nil, Fin.val_zero, add_zero,
        Bool.false_eq_true, ite_false,
        Prod.mk.injEq, Fin.ext_iff, decide_eq_false_iff_not, not_le]
      omega
    rw [addRaw, dite_eq_right hcond, hdc]
    simp [ih]

/-- `addRaw`'s "carry overflows the whole (empty) counter" base case: a fresh most-significant
    digit `1`, matching `prologueProg`'s `incPop` overflow branch. -/
lemma addRaw_nil_nil_true : addRaw ([] : List Digit) [] true = [1] := by
  have hcond : ¬ (([] : List Digit) = [] ∧ ([] : List Digit) = [] ∧ (true : Bool) = false) := by
    simp
  have hdc : addDigits (([] : List Digit).headD 0) (([] : List Digit).headD 0) true = (1, false) := by
    simp only [addDigits, List.headD_nil, Fin.val_zero, add_zero, ite_true]
    rfl
  rw [addRaw, dite_eq_right hcond, hdc]
  simp [List.tail, addRaw_nil_false]

/-- `addRaw`'s carry step on a leading `15` digit: `15 + 1` overflows base 16, wrapping to `0`
    and keeping the carry alive — matching `prologueProg`'s `incPop` carry branch. -/
lemma addRaw_cons_15 (rest : List Digit) :
    addRaw ((15 : Digit) :: rest) [] true = 0 :: addRaw rest [] true := by
  have hcond : ¬ ((15 : Digit) :: rest = [] ∧ ([] : List Digit) = [] ∧ (true : Bool) = false) := by
    simp
  have h15 : (15 : Digit).val = 15 := rfl
  have hdc : addDigits (((15 : Digit) :: rest).headD 0) (([] : List Digit).headD 0) true
      = (0, true) := by
    simp only [addDigits, List.headD_cons, List.headD_nil, Fin.val_zero, add_zero, ite_true, h15]
    refine Prod.ext ?_ ?_
    · apply Fin.ext; simp
    · simp
  rw [addRaw, dite_eq_right hcond, hdc]
  simp only [List.tail_cons, List.tail_nil]

/-- `addRaw`'s carry step on a leading non-`15` digit `d`: the carry resolves here, and the
    remaining digits are copied through unchanged (`addRaw_nil_false`) — matching
    `prologueProg`'s `incPop` resolve branch (which itself defers to `incCopyRest` for exactly
    this verbatim copy). -/
lemma addRaw_cons_resolve (d : Digit) (hd : d ≠ 15) (rest : List Digit) :
    addRaw (d :: rest) [] true = (d + 1) :: rest := by
  have hcond : ¬ (d :: rest = [] ∧ ([] : List Digit) = [] ∧ (true : Bool) = false) := by simp
  have hdlt : d.val < 15 := by
    have := d.isLt
    rcases Nat.lt_or_ge d.val 15 with h | h
    · exact h
    · exact absurd (by ext; omega : d = (15 : Digit)) hd
  have hdc : addDigits ((d :: rest).headD 0) (([] : List Digit).headD 0) true
      = (d + 1, false) := by
    simp only [addDigits, List.headD_cons, List.headD_nil, Fin.val_zero, add_zero, ite_true]
    refine Prod.ext ?_ ?_
    · apply Fin.ext
      simp only [Fin.val_add]
      have h1 : (1 : Digit).val = 1 := rfl
      omega
    · simp only [decide_eq_false_iff_not]; omega
  rw [addRaw, dite_eq_right hcond, hdc]
  simp only [List.tail_cons, List.tail_nil, addRaw_nil_false]

end NPComplete.RAMToTM

namespace NPComplete.RAMToTM.Generic

open NPComplete.BitCostRAM
open NPComplete.RAMToTM (MemSym)
open Turing Turing.TM2.Stmt

variable (p : List Instruction)

/-- The prologue's tree has one arm per `ProloguePhase` constructor and is written directly
    against the shared `Λg p` and `AllInstrState`. The prologue occurs once, so no site-dependent
    local-state embedding is needed. -/
def prologueProg : ProloguePhase → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState
  | .scanInput =>
      pop Kg.io (fun s ov => { s with prologue := ⟨ov, none⟩ })
        (branch (fun s => s.prologue.bit.isSome)
          (goto (fun _ => Λg.prologue .incPop))
          (push Kg.mem (fun _ => MemSym.entryEnd)
            (goto (fun _ => Λg.prologue .writeLength))))
  | .incPop =>
      pop (Kg.scratch .prologueCounter)
          (fun s ov => { s with prologue := { s.prologue with digit := ov } })
        (branch (fun s => s.prologue.digit.isSome)
          (branch (fun s => decide (s.prologue.digit.getD default = (15 : Digit)))
            (push (Kg.scratch .prologueWork) (fun _ => (0 : Digit))
              (goto (fun _ => Λg.prologue .incPop)))
            (push (Kg.scratch .prologueWork) (fun s => s.prologue.digit.getD default + 1)
              (goto (fun _ => Λg.prologue .incCopyRest))))
          (push (Kg.scratch .prologueWork) (fun _ => (1 : Digit))
            (goto (fun _ => Λg.prologue .incRestore))))
  | .incCopyRest =>
      pop (Kg.scratch .prologueCounter)
          (fun s ov => { s with prologue := { s.prologue with digit := ov } })
        (branch (fun s => s.prologue.digit.isSome)
          (push (Kg.scratch .prologueWork) (fun s => s.prologue.digit.getD default)
            (goto (fun _ => Λg.prologue .incCopyRest)))
          (goto (fun _ => Λg.prologue .incRestore)))
  | .incRestore =>
      pop (Kg.scratch .prologueWork)
          (fun s ov => { s with prologue := { s.prologue with digit := ov } })
        (branch (fun s => s.prologue.digit.isSome)
          (push (Kg.scratch .prologueCounter) (fun s => s.prologue.digit.getD default)
            (goto (fun _ => Λg.prologue .incRestore)))
          (branch (fun s => s.prologue.bit.getD false)
            (goto (fun _ => Λg.prologue .emitTrue))
            (goto (fun _ => Λg.prologue .scanInput))))
  | .emitTrue =>
      push Kg.mem (fun _ => MemSym.entryEnd)
        (push Kg.mem (fun _ => MemSym.digit 1)
          (push Kg.mem (fun _ => MemSym.addrEnd)
            (goto (fun _ => Λg.prologue .emitAddr))))
  | .emitAddr =>
      pop (Kg.scratch .prologueCounter)
          (fun s ov => { s with prologue := { s.prologue with digit := ov } })
        (branch (fun s => s.prologue.digit.isSome)
          (push Kg.mem (fun s => MemSym.digit (s.prologue.digit.getD default))
            (push (Kg.scratch .prologueWork) (fun s => s.prologue.digit.getD default)
              (goto (fun _ => Λg.prologue .emitAddr))))
          (goto (fun _ => Λg.prologue .emitAddrRestore)))
  | .emitAddrRestore =>
      pop (Kg.scratch .prologueWork)
          (fun s ov => { s with prologue := { s.prologue with digit := ov } })
        (branch (fun s => s.prologue.digit.isSome)
          (push (Kg.scratch .prologueCounter) (fun s => s.prologue.digit.getD default)
            (goto (fun _ => Λg.prologue .emitAddrRestore)))
          (goto (fun _ => Λg.prologue .scanInput)))
  | .writeLength =>
      pop (Kg.scratch .prologueCounter)
          (fun s ov => { s with prologue := { s.prologue with digit := ov } })
        (branch (fun s => s.prologue.digit.isSome)
          (push Kg.mem (fun s => MemSym.digit (s.prologue.digit.getD default))
            (goto (fun _ => Λg.prologue .writeLength)))
          (push Kg.mem (fun _ => MemSym.addrEnd)
            (goto (fun _ => Λg.prologue .done))))
  | .done => bridgeTo p 0

/-- Any dispatcher `M` that installs `prologueProg p` at every prologue label. This abstract
    contract lets the prologue's step lemmas be proved independently of `GenericDispatcher.lean`,
    as `SiteAgrees` does for each instruction's own realization. -/
def PrologueAgrees (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) : Prop :=
  ∀ ph, M (Λg.prologue ph) = prologueProg p ph

/-- One `TM2.step`, lifted to `Option` so it composes via `Function.iterate`. -/
def flipBindPrologue (p : List Instruction)
    (M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState) :
    Option (Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) →
      Option (Turing.TM2.Cfg (Γg p) (Λg p) AllInstrState) :=
  fun x => x.bind (Turing.TM2.step M)

variable {p : List Instruction} {M : Λg p → Turing.TM2.Stmt (Γg p) (Λg p) AllInstrState}

/-- Updating a key to the value it already has is a no-op — used throughout this file's step
    lemmas whenever a `pop`'s own key coincides with one already fixed by an incoming
    hypothesis (e.g. `scanInput`'s nil exit re-touches `Kg.io` with the empty list it already
    held). -/
lemma update_self_of_eq {K : Type} [DecidableEq K] {Γ : K → Type} (Sg : ∀ k, Γ k)
    (k : K) (v : Γ k) (h : Sg k = v) : Function.update Sg k v = Sg := by
  funext k'
  by_cases hk : k' = k
  · subst hk; simpa using h.symm
  · simp [Function.update, hk]

/-- Collapsing a re-update at `k1` past an intervening update at a *different* key `k2` — used
    throughout this file's aggregate (multi-step) lemmas, whose per-step lemmas each touch two
    stacks (e.g. `prologueCounter`/`prologueWork`) so a telescoped chain of steps re-touches the
    same key many times with an unrelated key's update sitting in between. -/
lemma update_update_comm_self {K : Type} [DecidableEq K] {Γ : K → Type} (Sg : ∀ k, Γ k)
    (k1 k2 : K) (hne : k1 ≠ k2) (v1 v1' : Γ k1) (v2 : Γ k2) :
    Function.update (Function.update (Function.update Sg k1 v1) k2 v2) k1 v1'
      = Function.update (Function.update Sg k1 v1') k2 v2 := by
  funext k
  by_cases h1 : k = k1
  · subst h1; simp [Function.update_self, Function.update_of_ne hne]
  · by_cases h2 : k = k2
    · subst h2; simp [Function.update_self, Function.update_of_ne hne.symm]
    · simp [Function.update_of_ne h1, Function.update_of_ne h2]

/-- Three-key generalization of `update_update_comm_self`: collapsing a re-update at `k1` past
    two intervening updates at distinct keys `k2`/`k3` — needed by `emitAddr`'s aggregate lemma,
    whose per-step lemma touches three stacks (`prologueCounter`/`Kg.mem`/`prologueWork`) at
    once, unlike every other phase's two-stack shape. -/
lemma update_update_update_comm_self {K : Type} [DecidableEq K] {Γ : K → Type} (Sg : ∀ k, Γ k)
    (k1 k2 k3 : K) (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3)
    (v1 v1' : Γ k1) (v2 : Γ k2) (v3 : Γ k3) :
    Function.update
        (Function.update (Function.update (Function.update Sg k1 v1) k2 v2) k3 v3) k1 v1'
      = Function.update (Function.update (Function.update Sg k1 v1') k2 v2) k3 v3 := by
  funext k
  by_cases h1 : k = k1
  · subst h1; simp [Function.update_of_ne h13, Function.update_of_ne h12]
  · by_cases h2 : k = k2
    · subst h2
      simp [Function.update_of_ne (Ne.symm h12), Function.update_of_ne h23]
    · by_cases h3 : k = k3
      · subst h3; simp [Function.update_of_ne (Ne.symm h13)]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]

/-- `scanInput` on a nonempty `Kg.io`: pop the next bit into `AllInstrState.prologue.bit`
    (resetting `digit`, unused until the increment sub-sequence writes it) and move to
    `incPop` — regardless of the bit's value, since the address counter advances for every bit. -/
lemma prologue_step_scanInput_some (hAgrees : PrologueAgrees p M) (b : Bool)
    (restIo : List Bool) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hIo : Sg Kg.io = b :: restIo) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .scanInput), var, Sg⟩)
      = some ⟨some (Λg.prologue .incPop), { var with prologue := ⟨some b, none⟩ },
          Function.update Sg Kg.io restIo⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .scanInput), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .scanInput, prologueProg, hIo]

/-- `scanInput` on an exhausted `Kg.io`: push the length entry's `entryEnd` marker and move to
    `writeLength`, which will drain `prologueCounter` (now holding `bits.length`'s digits) onto
    `Kg.mem` to finish that entry. `prologue`'s scratch resets to `⟨none, none⟩` — not literally
    unchanged, since a loop-back arrival here (via `incRestore`'s `false`-bit branch) can still
    have a stale `bit` from the previous iteration that this pop overwrites. -/
lemma prologue_step_scanInput_nil (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hIo : Sg Kg.io = ([] : List Bool)) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .scanInput), var, Sg⟩)
      = some ⟨some (Λg.prologue .writeLength), { var with prologue := ⟨none, none⟩ },
          Function.update Sg Kg.mem (MemSym.entryEnd :: Sg Kg.mem)⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .scanInput), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .scanInput, prologueProg, hIo,
    update_self_of_eq Sg Kg.io [] hIo]

/-- `incPop` on a leading `15` digit: `15 + 1` overflows base 16, so this pushes the wrapped
    digit `0` onto `prologueWork` and loops back to `incPop` to keep rippling the carry through
    the next digit. -/
lemma prologue_step_incPop_carry (hAgrees : PrologueAgrees p M) (rest : List Digit)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = (15 : Digit) :: rest) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .incPop), var, Sg⟩)
      = some ⟨some (Λg.prologue .incPop),
          { var with prologue := { var.prologue with digit := some 15 } },
          Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest)
            (Kg.scratch .prologueWork) ((0 : Digit) :: Sg (Kg.scratch .prologueWork))⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .incPop), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .incPop, prologueProg, hCounter]

/-- `incPop` on a leading non-`15` digit `d`: the carry resolves here (`d + 1` fits in one
    digit), so this pushes `d + 1` onto `prologueWork` and moves to `incCopyRest` to copy
    whatever remains verbatim. -/
lemma prologue_step_incPop_resolve (hAgrees : PrologueAgrees p M) (d : Digit) (hd : d ≠ 15)
    (rest : List Digit) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = d :: rest) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .incPop), var, Sg⟩)
      = some ⟨some (Λg.prologue .incCopyRest),
          { var with prologue := { var.prologue with digit := some d } },
          Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest)
            (Kg.scratch .prologueWork) ((d + 1) :: Sg (Kg.scratch .prologueWork))⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .incPop), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .incPop, prologueProg, hCounter, hd]

/-- `incPop` on an exhausted `prologueCounter`: the carry rippled through every digit (all
    `15`s, or the counter started at `0`), so a fresh most-significant digit `1` is pushed and
    the machine moves straight to `incRestore` — `incCopyRest` is skipped entirely since there
    is nothing left to copy verbatim. -/
lemma prologue_step_incPop_overflow (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hCounter : Sg (Kg.scratch .prologueCounter) = ([] : List Digit)) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .incPop), var, Sg⟩)
      = some ⟨some (Λg.prologue .incRestore),
          { var with prologue := { var.prologue with digit := none } },
          Function.update Sg (Kg.scratch .prologueWork)
            ((1 : Digit) :: Sg (Kg.scratch .prologueWork))⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .incPop), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .incPop, prologueProg, hCounter,
    update_self_of_eq Sg (Kg.scratch .prologueCounter) [] hCounter]

/-- `incCopyRest` on a nonempty `prologueCounter`: the carry has already resolved, so this just
    copies the next digit verbatim onto `prologueWork` and loops. -/
lemma prologue_step_incCopyRest_cons (hAgrees : PrologueAgrees p M) (d : Digit)
    (rest : List Digit) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = d :: rest) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .incCopyRest), var, Sg⟩)
      = some ⟨some (Λg.prologue .incCopyRest),
          { var with prologue := { var.prologue with digit := some d } },
          Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest)
            (Kg.scratch .prologueWork) (d :: Sg (Kg.scratch .prologueWork))⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .incCopyRest), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .incCopyRest, prologueProg, hCounter]

/-- `incCopyRest` on an exhausted `prologueCounter`: nothing left to copy, move to
    `incRestore`. -/
lemma prologue_step_incCopyRest_nil (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hCounter : Sg (Kg.scratch .prologueCounter) = ([] : List Digit)) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .incCopyRest), var, Sg⟩)
      = some ⟨some (Λg.prologue .incRestore),
          { var with prologue := { var.prologue with digit := none } }, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .incCopyRest), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .incCopyRest, prologueProg, hCounter,
    update_self_of_eq Sg (Kg.scratch .prologueCounter) [] hCounter]

/-- `incRestore` on a nonempty `prologueWork`: pop one digit and push it back onto
    `prologueCounter`, restoring the pop-then-push reversal `incPop`/`incCopyRest` introduced
    (mirroring `Store2Phase.copyValueRestore`). -/
lemma prologue_step_incRestore_cons (hAgrees : PrologueAgrees p M) (d : Digit)
    (rest : List Digit) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hWork : Sg (Kg.scratch .prologueWork) = d :: rest) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .incRestore), var, Sg⟩)
      = some ⟨some (Λg.prologue .incRestore),
          { var with prologue := { var.prologue with digit := some d } },
          Function.update (Function.update Sg (Kg.scratch .prologueWork) rest)
            (Kg.scratch .prologueCounter) (d :: Sg (Kg.scratch .prologueCounter))⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .incRestore), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .incRestore, prologueProg, hWork]

/-- `incRestore` on an exhausted `prologueWork` with a `true` stashed bit: the counter is fully
    restored (now holding the incremented value), so this needs an entry — move to `emitTrue`. -/
lemma prologue_step_incRestore_nil_true (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hWork : Sg (Kg.scratch .prologueWork) = ([] : List Digit))
    (hBit : var.prologue.bit = some true) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .incRestore), var, Sg⟩)
      = some ⟨some (Λg.prologue .emitTrue),
          { var with prologue := { var.prologue with digit := none } }, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .incRestore), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .incRestore, prologueProg, hWork, hBit,
    update_self_of_eq Sg (Kg.scratch .prologueWork) [] hWork]

/-- `incRestore` on an exhausted `prologueWork` with a `false` stashed bit: no entry needed,
    loop back to `scanInput` for the next bit. -/
lemma prologue_step_incRestore_nil_false (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hWork : Sg (Kg.scratch .prologueWork) = ([] : List Digit))
    (hBit : var.prologue.bit = some false) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .incRestore), var, Sg⟩)
      = some ⟨some (Λg.prologue .scanInput),
          { var with prologue := { var.prologue with digit := none } }, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .incRestore), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .incRestore, prologueProg, hWork, hBit,
    update_self_of_eq Sg (Kg.scratch .prologueWork) [] hWork]

/-- `emitTrue`'s whole 3-push chain in one step: the value field is always the single digit `1`
    (matching `encodeEntry (i+1) 1`'s value side), so no loop is needed. -/
lemma prologue_step_emitTrue (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .emitTrue), var, Sg⟩)
      = some ⟨some (Λg.prologue .emitAddr), var,
          Function.update Sg Kg.mem
            (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: Sg Kg.mem)⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .emitTrue), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .emitTrue, prologueProg]

/-- `done` resets to canonical and bridges to the RAM's initial `pc = 0`, exactly like every
    `exec`-site's own `done`-bridge (`bridgeTo`). -/
lemma prologue_step_done (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .done), var, Sg⟩)
      = some ⟨some (entryAt p 0), AllInstrState.canonical, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .done), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .done, prologueProg, bridgeTo]

/-- `emitAddr` on a nonempty `prologueCounter`: non-destructively copy one digit onto `Kg.mem`
    (which `push`'s prepend flips to MSB-first, `MemoryEncoding.lean`'s module docstring) while
    also stashing it onto `prologueWork` for `emitAddrRestore` to replay back. -/
lemma prologue_step_emitAddr_cons (hAgrees : PrologueAgrees p M) (d : Digit) (rest : List Digit)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = d :: rest) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .emitAddr), var, Sg⟩)
      = some ⟨some (Λg.prologue .emitAddr),
          { var with prologue := { var.prologue with digit := some d } },
          Function.update
            (Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest)
              Kg.mem (MemSym.digit d :: Sg Kg.mem))
            (Kg.scratch .prologueWork) (d :: Sg (Kg.scratch .prologueWork))⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .emitAddr), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .emitAddr, prologueProg, hCounter]

/-- `emitAddr` on an exhausted `prologueCounter`: the whole address has been copied onto
    `Kg.mem`, move to `emitAddrRestore` to undo the non-destructive copy. -/
lemma prologue_step_emitAddr_nil (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hCounter : Sg (Kg.scratch .prologueCounter) = ([] : List Digit)) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .emitAddr), var, Sg⟩)
      = some ⟨some (Λg.prologue .emitAddrRestore),
          { var with prologue := { var.prologue with digit := none } }, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .emitAddr), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .emitAddr, prologueProg, hCounter,
    update_self_of_eq Sg (Kg.scratch .prologueCounter) [] hCounter]

/-- `emitAddrRestore` on a nonempty `prologueWork`: pop one stashed digit and push it back onto
    `prologueCounter`, undoing `emitAddr`'s non-destructive copy one digit at a time. -/
lemma prologue_step_emitAddrRestore_cons (hAgrees : PrologueAgrees p M) (d : Digit)
    (rest : List Digit) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hWork : Sg (Kg.scratch .prologueWork) = d :: rest) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .emitAddrRestore), var, Sg⟩)
      = some ⟨some (Λg.prologue .emitAddrRestore),
          { var with prologue := { var.prologue with digit := some d } },
          Function.update (Function.update Sg (Kg.scratch .prologueWork) rest)
            (Kg.scratch .prologueCounter) (d :: Sg (Kg.scratch .prologueCounter))⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .emitAddrRestore), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .emitAddrRestore, prologueProg, hWork]

/-- `emitAddrRestore` on an exhausted `prologueWork`: `prologueCounter` is fully restored, loop
    back to `scanInput` for the next bit. -/
lemma prologue_step_emitAddrRestore_nil (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hWork : Sg (Kg.scratch .prologueWork) = ([] : List Digit)) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .emitAddrRestore), var, Sg⟩)
      = some ⟨some (Λg.prologue .scanInput),
          { var with prologue := { var.prologue with digit := none } }, Sg⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .emitAddrRestore), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .emitAddrRestore, prologueProg, hWork,
    update_self_of_eq Sg (Kg.scratch .prologueWork) [] hWork]

/-- `writeLength` on a nonempty `prologueCounter`: destructively drain one digit of the bit
    length (now sitting on `prologueCounter`, incremented once per scanned bit) straight onto
    `Kg.mem` — no restore needed, since the length entry is the last thing `Kg.mem` ever needs
    from this counter (`Represents`'s scratch-empty requirement wants it drained anyway). -/
lemma prologue_step_writeLength_cons (hAgrees : PrologueAgrees p M) (d : Digit)
    (rest : List Digit) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = d :: rest) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .writeLength), var, Sg⟩)
      = some ⟨some (Λg.prologue .writeLength),
          { var with prologue := { var.prologue with digit := some d } },
          Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest)
            Kg.mem (MemSym.digit d :: Sg Kg.mem)⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .writeLength), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .writeLength, prologueProg, hCounter]

/-- `writeLength` on an exhausted `prologueCounter`: the length entry's address field (`0`,
    i.e. no digits at all — `natToDigits 0 = []`) needs only its `addrEnd` marker; move to
    `done`. -/
lemma prologue_step_writeLength_nil (hAgrees : PrologueAgrees p M) (var : AllInstrState)
    (Sg : ∀ k, List (Γg p k)) (hCounter : Sg (Kg.scratch .prologueCounter) = ([] : List Digit)) :
    flipBindPrologue p M (some ⟨some (Λg.prologue .writeLength), var, Sg⟩)
      = some ⟨some (Λg.prologue .done),
          { var with prologue := { var.prologue with digit := none } },
          Function.update Sg Kg.mem (MemSym.addrEnd :: Sg Kg.mem)⟩ := by
  show (Turing.TM2.step M) ⟨some (Λg.prologue .writeLength), var, Sg⟩ = _
  simp [Turing.TM2.step, Turing.TM2.stepAux, hAgrees .writeLength, prologueProg, hCounter,
    update_self_of_eq Sg (Kg.scratch .prologueCounter) [] hCounter]

/-- `incCopyRest`'s aggregate effect: copying `rest` verbatim takes `rest.length + 1` steps
    (one per digit, plus one for the final empty check, matching `DigitAdd.lean`'s own
    `addRaw`-step-count discussion) and leaves it reversed onto whatever `prologueWork` already
    held — `push` always prepending is what flips the read order (`MemoryEncoding.lean`'s module
    docstring). -/
lemma prologue_incCopyRest_run (hAgrees : PrologueAgrees p M) (rest w0 : List Digit)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = rest)
    (hWork : Sg (Kg.scratch .prologueWork) = w0) :
    (flipBindPrologue p M)^[rest.length + 1] (some ⟨some (Λg.prologue .incCopyRest), var, Sg⟩)
      = some ⟨some (Λg.prologue .incRestore),
          { var with prologue := { var.prologue with digit := none } },
          Function.update (Function.update Sg (Kg.scratch .prologueCounter) [])
            (Kg.scratch .prologueWork) (rest.reverse ++ w0)⟩ := by
  induction rest generalizing var w0 Sg with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
      List.nil_append]
    rw [prologue_step_incCopyRest_nil hAgrees var Sg hCounter,
      update_self_of_eq Sg (Kg.scratch .prologueCounter) [] hCounter,
      update_self_of_eq Sg (Kg.scratch .prologueWork) w0 hWork]
  | cons d rest' ih =>
    have hstep := prologue_step_incCopyRest_cons hAgrees d rest' var Sg hCounter
    rw [show (d :: rest').length + 1 = (rest'.length + 1) + 1 from by
        simp only [List.length_cons],
      Function.iterate_succ_apply, hstep]
    rw [ih (d :: w0) { var with prologue := { var.prologue with digit := some d } }
        (Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest')
          (Kg.scratch .prologueWork) (d :: Sg (Kg.scratch .prologueWork)))
        (by simp) (by simp [hWork])]
    rw [update_update_comm_self Sg (Kg.scratch .prologueCounter) (Kg.scratch .prologueWork)
      (by simp) rest' [] (d :: Sg (Kg.scratch .prologueWork))]
    simp [List.reverse_cons, List.append_assoc]

/-- `incPop`'s aggregate effect: `counter.length + 1` steps (matching `incCopyRest_run`'s own
    step-count shape) take it to `incRestore` with `prologueCounter` drained and `prologueWork`
    holding `(addRaw counter [] true).reverse` prepended onto whatever it already had — the
    TM-level realization of `addRaw`'s pure "add one with carry" recursion
    (`addRaw_cons_15`/`addRaw_cons_resolve`/`addRaw_nil_nil_true` drive the three branches). The
    stashed `bit` survives unchanged throughout (needed by `incRestore`'s own dispatch once this
    finishes). -/
lemma prologue_incPop_run (hAgrees : PrologueAgrees p M) (counter w0 : List Digit)
    (bitVal : Bool) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = counter)
    (hWork : Sg (Kg.scratch .prologueWork) = w0)
    (hBit : var.prologue.bit = some bitVal) :
    ∃ var', var'.prologue.bit = some bitVal ∧
      (flipBindPrologue p M)^[counter.length + 1] (some ⟨some (Λg.prologue .incPop), var, Sg⟩)
        = some ⟨some (Λg.prologue .incRestore), var',
            Function.update (Function.update Sg (Kg.scratch .prologueCounter) [])
              (Kg.scratch .prologueWork) ((addRaw counter [] true).reverse ++ w0)⟩ := by
  induction counter generalizing w0 var Sg with
  | nil =>
    refine ⟨{ var with prologue := { var.prologue with digit := none } }, hBit, ?_⟩
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, addRaw_nil_nil_true,
      List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [update_self_of_eq Sg (Kg.scratch .prologueCounter) [] hCounter, ← hWork]
    exact prologue_step_incPop_overflow hAgrees var Sg hCounter
  | cons d rest ih =>
    by_cases hd : d = 15
    · subst hd
      have hstep := prologue_step_incPop_carry hAgrees rest var Sg hCounter
      obtain ⟨var', hvar', hrun⟩ := ih (0 :: w0)
        { var with prologue := { var.prologue with digit := some (15 : Digit) } }
        (Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest)
          (Kg.scratch .prologueWork) ((0 : Digit) :: Sg (Kg.scratch .prologueWork)))
        (by simp) (by simp [hWork]) hBit
      refine ⟨var', hvar', ?_⟩
      rw [show ((15 : Digit) :: rest).length + 1 = (rest.length + 1) + 1 from by
          simp only [List.length_cons],
        Function.iterate_succ_apply, hstep, hrun,
        update_update_comm_self Sg (Kg.scratch .prologueCounter) (Kg.scratch .prologueWork)
          (by simp) rest [] ((0 : Digit) :: Sg (Kg.scratch .prologueWork)),
        addRaw_cons_15, List.reverse_cons, List.append_assoc]
      simp [hWork]
    · have hstep := prologue_step_incPop_resolve hAgrees d hd rest var Sg hCounter
      have hrun := prologue_incCopyRest_run hAgrees rest ((d + 1) :: w0)
        { var with prologue := { var.prologue with digit := some d } }
        (Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest)
          (Kg.scratch .prologueWork) ((d + 1) :: Sg (Kg.scratch .prologueWork)))
        (by simp) (by simp [hWork])
      refine ⟨{ var with prologue := { var.prologue with digit := none } }, hBit, ?_⟩
      rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by
          simp only [List.length_cons],
        Function.iterate_succ_apply, hstep, hrun,
        update_update_comm_self Sg (Kg.scratch .prologueCounter) (Kg.scratch .prologueWork)
          (by simp) rest [] ((d + 1) :: Sg (Kg.scratch .prologueWork)),
        addRaw_cons_resolve d hd, List.reverse_cons, List.append_assoc]
      simp [hWork]

/-- `incRestore`'s aggregate effect: `work.length + 1` steps drain `prologueWork` entirely,
    rebuilding `work.reverse` onto `prologueCounter` (undoing `incPop`/`incCopyRest`'s own
    reversal, so a full `incPop_run` + `incRestore_run` round trip nets *no* reversal — exactly
    `addRaw counter [] true` sitting LSB-first on `prologueCounter` again), then dispatches on
    the stashed bit to `emitTrue` or back to `scanInput`. -/
lemma prologue_incRestore_run (hAgrees : PrologueAgrees p M) (work c0 : List Digit)
    (bitVal : Bool) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hWork : Sg (Kg.scratch .prologueWork) = work)
    (hCounter : Sg (Kg.scratch .prologueCounter) = c0)
    (hBit : var.prologue.bit = some bitVal) :
    (flipBindPrologue p M)^[work.length + 1] (some ⟨some (Λg.prologue .incRestore), var, Sg⟩)
      = some ⟨some (Λg.prologue (if bitVal then .emitTrue else .scanInput)),
          { var with prologue := { var.prologue with digit := none } },
          Function.update (Function.update Sg (Kg.scratch .prologueWork) [])
            (Kg.scratch .prologueCounter) (work.reverse ++ c0)⟩ := by
  induction work generalizing var c0 Sg with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
      List.nil_append]
    rw [update_self_of_eq Sg (Kg.scratch .prologueWork) [] hWork, ← hCounter]
    cases bitVal with
    | false => simpa using prologue_step_incRestore_nil_false hAgrees var Sg hWork hBit
    | true => simpa using prologue_step_incRestore_nil_true hAgrees var Sg hWork hBit
  | cons d rest ih =>
    have hstep := prologue_step_incRestore_cons hAgrees d rest var Sg hWork
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by
        simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih (d :: c0) { var with prologue := { var.prologue with digit := some d } }
        (Function.update (Function.update Sg (Kg.scratch .prologueWork) rest)
          (Kg.scratch .prologueCounter) (d :: Sg (Kg.scratch .prologueCounter)))
        (by simp) (by simp [hCounter]) hBit,
      update_update_comm_self Sg (Kg.scratch .prologueWork) (Kg.scratch .prologueCounter)
        (by simp) rest [] (d :: Sg (Kg.scratch .prologueCounter))]
    simp [List.reverse_cons, List.append_assoc]

/-- Composing `incPop_run` and `incRestore_run`: entering `.incPop` with `prologueCounter`
    holding `counter` and `prologueWork` empty (the invariant every arrival from `scanInput`
    satisfies), `counter.length + (addRaw counter [] true).length + 2` steps process the one
    bit's increment and land at `.emitTrue` (bit `true`) or back at `.scanInput` (bit `false`)
    with `prologueCounter = addRaw counter [] true` and `prologueWork` empty again —
    `incPop`'s reversal and `incRestore`'s own reversal exactly cancel (`List.reverse_reverse`),
    so no explicit reversal survives the round trip. -/
lemma prologue_inc_bit_run (hAgrees : PrologueAgrees p M) (counter : List Digit)
    (bitVal : Bool) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = counter)
    (hWork : Sg (Kg.scratch .prologueWork) = ([] : List Digit))
    (hBit : var.prologue.bit = some bitVal) :
    ∃ var', var'.prologue.bit = some bitVal ∧
      (flipBindPrologue p M)^[counter.length + (addRaw counter [] true).length + 2]
          (some ⟨some (Λg.prologue .incPop), var, Sg⟩)
        = some ⟨some (Λg.prologue (if bitVal then .emitTrue else .scanInput)), var',
            Function.update
              (Function.update Sg (Kg.scratch .prologueCounter) (addRaw counter [] true))
              (Kg.scratch .prologueWork) []⟩ := by
  obtain ⟨var1, hvar1, hrun1⟩ :=
    prologue_incPop_run hAgrees counter [] bitVal var Sg hCounter hWork hBit
  have hrun2 := prologue_incRestore_run hAgrees (addRaw counter [] true).reverse [] bitVal var1
    (Function.update (Function.update Sg (Kg.scratch .prologueCounter) [])
      (Kg.scratch .prologueWork) ((addRaw counter [] true).reverse ++ ([] : List Digit)))
    (by simp) (by simp) hvar1
  refine ⟨{ var1 with prologue := { var1.prologue with digit := none } }, by simp [hvar1], ?_⟩
  rw [show counter.length + (addRaw counter [] true).length + 2
      = ((addRaw counter [] true).reverse.length + 1) + (counter.length + 1) from by
      simp only [List.length_reverse]; omega,
    Function.iterate_add_apply, hrun1, hrun2]
  simp only [Function.update_idem]
  rw [update_update_comm_self Sg (Kg.scratch .prologueCounter) (Kg.scratch .prologueWork)
    (by simp) [] ((addRaw counter [] true).reverse.reverse ++ ([] : List Digit)) []]
  simp [List.reverse_reverse]

/-- `emitAddr`'s aggregate effect: `counter.length + 1` steps drain `prologueCounter` entirely,
    non-destructively copying it (per-digit) onto both `Kg.mem` (the permanent MSB-first address
    entry, `push`'s prepend flipping the pop order — `MemoryEncoding.lean`'s docstring) and
    `prologueWork` (a same-order stash for `emitAddrRestore` to replay back onto
    `prologueCounter`), then moves to `emitAddrRestore`. -/
lemma prologue_emitAddr_run (hAgrees : PrologueAgrees p M) (counter w0 : List Digit)
    (m0 : List MemSym) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = counter)
    (hWork : Sg (Kg.scratch .prologueWork) = w0) (hMem : Sg Kg.mem = m0) :
    (flipBindPrologue p M)^[counter.length + 1]
        (some ⟨some (Λg.prologue .emitAddr), var, Sg⟩)
      = some ⟨some (Λg.prologue .emitAddrRestore),
          { var with prologue := { var.prologue with digit := none } },
          Function.update
            (Function.update (Function.update Sg (Kg.scratch .prologueCounter) [])
              Kg.mem (counter.reverse.map MemSym.digit ++ m0))
            (Kg.scratch .prologueWork) (counter.reverse ++ w0)⟩ := by
  induction counter generalizing var w0 m0 Sg with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
      List.map_nil, List.nil_append]
    rw [update_self_of_eq Sg (Kg.scratch .prologueCounter) [] hCounter, ← hMem, ← hWork]
    simpa using prologue_step_emitAddr_nil hAgrees var Sg hCounter
  | cons d rest ih =>
    have hstep := prologue_step_emitAddr_cons hAgrees d rest var Sg hCounter
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by
        simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih (d :: w0) (MemSym.digit d :: m0)
        { var with prologue := { var.prologue with digit := some d } }
        (Function.update
          (Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest)
            Kg.mem (MemSym.digit d :: Sg Kg.mem))
          (Kg.scratch .prologueWork) (d :: Sg (Kg.scratch .prologueWork)))
        (by simp) (by simp [hWork]) (by simp [hMem]),
      update_update_update_comm_self Sg (Kg.scratch .prologueCounter) Kg.mem
        (Kg.scratch .prologueWork) (by simp) (by simp) (by simp) rest []
        (MemSym.digit d :: Sg Kg.mem) (d :: Sg (Kg.scratch .prologueWork)),
      update_update_comm_self (Function.update Sg (Kg.scratch .prologueCounter) []) Kg.mem
        (Kg.scratch .prologueWork) (by simp) (MemSym.digit d :: Sg Kg.mem)
        (rest.reverse.map MemSym.digit ++ (MemSym.digit d :: m0)) (d :: Sg (Kg.scratch .prologueWork))]
    simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- `emitAddrRestore`'s aggregate effect: `work.length + 1` steps drain `prologueWork` entirely,
    rebuilding `work.reverse` onto `prologueCounter` (undoing `emitAddr`'s non-destructive copy),
    then loops back to `scanInput` unconditionally — unlike `incRestore_run`, no stashed-bit
    dispatch is needed here since `emitTrue`'s address digits are always followed by the next
    bit scan. -/
lemma prologue_emitAddrRestore_run (hAgrees : PrologueAgrees p M) (work c0 : List Digit)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hWork : Sg (Kg.scratch .prologueWork) = work)
    (hCounter : Sg (Kg.scratch .prologueCounter) = c0) :
    (flipBindPrologue p M)^[work.length + 1]
        (some ⟨some (Λg.prologue .emitAddrRestore), var, Sg⟩)
      = some ⟨some (Λg.prologue .scanInput),
          { var with prologue := { var.prologue with digit := none } },
          Function.update (Function.update Sg (Kg.scratch .prologueWork) [])
            (Kg.scratch .prologueCounter) (work.reverse ++ c0)⟩ := by
  induction work generalizing var c0 Sg with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
      List.nil_append]
    rw [update_self_of_eq Sg (Kg.scratch .prologueWork) [] hWork, ← hCounter]
    simpa using prologue_step_emitAddrRestore_nil hAgrees var Sg hWork
  | cons d rest ih =>
    have hstep := prologue_step_emitAddrRestore_cons hAgrees d rest var Sg hWork
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by
        simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih (d :: c0) { var with prologue := { var.prologue with digit := some d } }
        (Function.update (Function.update Sg (Kg.scratch .prologueWork) rest)
          (Kg.scratch .prologueCounter) (d :: Sg (Kg.scratch .prologueCounter)))
        (by simp) (by simp [hCounter]),
      update_update_comm_self Sg (Kg.scratch .prologueWork) (Kg.scratch .prologueCounter)
        (by simp) rest [] (d :: Sg (Kg.scratch .prologueCounter))]
    simp [List.reverse_cons, List.append_assoc]

/-- `writeLength`'s aggregate effect: `counter.length + 1` steps destructively drain
    `prologueCounter` onto `Kg.mem` MSB-first (`counter.reverse.map MemSym.digit`, no restore —
    the length entry is `Kg.mem`'s last use of this counter, matching `Represents`'s
    scratch-empty requirement), then pushes the `addrEnd` marker and moves to `done`. -/
lemma prologue_writeLength_run (hAgrees : PrologueAgrees p M) (counter : List Digit)
    (m0 : List MemSym) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = counter) (hMem : Sg Kg.mem = m0) :
    (flipBindPrologue p M)^[counter.length + 1]
        (some ⟨some (Λg.prologue .writeLength), var, Sg⟩)
      = some ⟨some (Λg.prologue .done),
          { var with prologue := { var.prologue with digit := none } },
          Function.update (Function.update Sg (Kg.scratch .prologueCounter) [])
            Kg.mem (MemSym.addrEnd :: (counter.reverse.map MemSym.digit ++ m0))⟩ := by
  induction counter generalizing var m0 Sg with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
      List.map_nil, List.nil_append]
    rw [update_self_of_eq Sg (Kg.scratch .prologueCounter) [] hCounter, ← hMem]
    simpa using prologue_step_writeLength_nil hAgrees var Sg hCounter
  | cons d rest ih =>
    have hstep := prologue_step_writeLength_cons hAgrees d rest var Sg hCounter
    rw [show (d :: rest).length + 1 = (rest.length + 1) + 1 from by
        simp only [List.length_cons],
      Function.iterate_succ_apply, hstep,
      ih (MemSym.digit d :: m0) { var with prologue := { var.prologue with digit := some d } }
        (Function.update (Function.update Sg (Kg.scratch .prologueCounter) rest)
          Kg.mem (MemSym.digit d :: Sg Kg.mem))
        (by simp) (by simp [hMem]),
      update_update_comm_self Sg (Kg.scratch .prologueCounter) Kg.mem
        (by simp) rest [] (MemSym.digit d :: Sg Kg.mem)]
    simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- `emitTrue`+`emitAddr`+`emitAddrRestore` fused: from `.emitTrue`, `2 * counter.length + 3`
    steps push the fixed `entryEnd`/`digit 1`/`addrEnd` markers, non-destructively copy the
    address counter's digits onto `Kg.mem` (MSB-first) and restore `prologueCounter`/
    `prologueWork` to their values on entry (the copy-then-restore round trip), landing back at
    `.scanInput`. -/
lemma prologue_emitTrue_entry_run (hAgrees : PrologueAgrees p M) (counter : List Digit)
    (m0 : List MemSym) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = counter)
    (hWork : Sg (Kg.scratch .prologueWork) = ([] : List Digit)) (hMem : Sg Kg.mem = m0) :
    (flipBindPrologue p M)^[2 * counter.length + 3]
        (some ⟨some (Λg.prologue .emitTrue), var, Sg⟩)
      = some ⟨some (Λg.prologue .scanInput),
          { var with prologue := { var.prologue with digit := none } },
          Function.update
            (Function.update
              (Function.update Sg Kg.mem
                (counter.reverse.map MemSym.digit ++
                  (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: m0)))
              (Kg.scratch .prologueCounter) counter)
            (Kg.scratch .prologueWork) []⟩ := by
  have hstep := prologue_step_emitTrue hAgrees var Sg
  set Sg1 := Function.update Sg Kg.mem
    (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: Sg Kg.mem) with hSg1
  have hrun1 := prologue_emitAddr_run hAgrees counter []
    (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: Sg Kg.mem) var Sg1
    (by simp [hSg1, hCounter]) (by simp [hSg1, hWork]) (by simp [hSg1])
  set Sg2 := Function.update
    (Function.update (Function.update Sg1 (Kg.scratch .prologueCounter) [])
      Kg.mem (counter.reverse.map MemSym.digit ++
        (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: Sg Kg.mem)))
    (Kg.scratch .prologueWork) (counter.reverse ++ ([] : List Digit)) with hSg2
  have hrun2 := prologue_emitAddrRestore_run hAgrees counter.reverse []
    { var with prologue := { var.prologue with digit := none } } Sg2
    (by simp [hSg2]) (by simp [hSg2, hSg1])
  rw [show 2 * counter.length + 3
      = ((counter.reverse.length + 1) + (counter.length + 1)) + 1 from by
      simp only [List.length_reverse]; omega,
    Function.iterate_add_apply, Function.iterate_one, hstep,
    Function.iterate_add_apply, hrun1, hrun2, hSg2, hSg1]
  simp only [Function.update_idem]
  rw [update_update_update_comm_self (Function.update Sg Kg.mem
      (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: Sg Kg.mem))
    (Kg.scratch .prologueCounter) Kg.mem (Kg.scratch .prologueWork) (by simp) (by simp) (by simp)
    [] (counter.reverse.reverse ++ ([] : List Digit))
    (counter.reverse.map MemSym.digit ++ (MemSym.addrEnd :: MemSym.digit 1 ::
      MemSym.entryEnd :: Sg Kg.mem)) []]
  rw [update_update_comm_self Sg Kg.mem (Kg.scratch .prologueCounter) (by simp)
    (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: Sg Kg.mem)
    (counter.reverse.map MemSym.digit ++ (MemSym.addrEnd :: MemSym.digit 1 ::
      MemSym.entryEnd :: Sg Kg.mem)) (counter.reverse.reverse ++ ([] : List Digit))]
  simp [hMem, List.reverse_reverse]

/-- Full one-bit dispatch: from `.incPop`, processes the address-counter increment
    (`incBit_run`) and, only when the bit is `true`, also emits the length/address/value entry
    (`emitTrueEntry_run`), landing back at `.scanInput` either way with `prologueCounter =
    addRaw counter [] true` and `prologueWork` empty — the invariant the next bit's `incPop`
    dispatch needs. `Kg.mem` gains a new entry exactly when `bitVal = true`. -/
lemma prologue_process_bit_run (hAgrees : PrologueAgrees p M) (counter : List Digit)
    (bitVal : Bool) (m0 : List MemSym) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hCounter : Sg (Kg.scratch .prologueCounter) = counter)
    (hWork : Sg (Kg.scratch .prologueWork) = ([] : List Digit))
    (hMem : Sg Kg.mem = m0) (hBit : var.prologue.bit = some bitVal) :
    ∃ var', (flipBindPrologue p M)^[counter.length + (addRaw counter [] true).length + 2 +
          (if bitVal then 2 * (addRaw counter [] true).length + 3 else 0)]
        (some ⟨some (Λg.prologue .incPop), var, Sg⟩)
      = some ⟨some (Λg.prologue .scanInput), var',
          if bitVal then
            Function.update
              (Function.update
                (Function.update Sg Kg.mem
                  ((addRaw counter [] true).reverse.map MemSym.digit ++
                    (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: m0)))
                (Kg.scratch .prologueCounter) (addRaw counter [] true))
              (Kg.scratch .prologueWork) []
          else
            Function.update
              (Function.update Sg (Kg.scratch .prologueCounter) (addRaw counter [] true))
              (Kg.scratch .prologueWork) []⟩ := by
  obtain ⟨var1, hvar1, hrun1⟩ := prologue_inc_bit_run hAgrees counter bitVal var Sg hCounter hWork hBit
  cases bitVal with
  | false => exact ⟨var1, by simpa using hrun1⟩
  | true =>
    have hrun2 := prologue_emitTrue_entry_run hAgrees (addRaw counter [] true) m0 var1
      (Function.update (Function.update Sg (Kg.scratch .prologueCounter)
          (addRaw counter [] true)) (Kg.scratch .prologueWork) [])
      (by simp) (by simp) (by simp [hMem])
    refine ⟨{ var1 with prologue := { var1.prologue with digit := none } }, ?_⟩
    simp only [reduceIte] at hrun1 ⊢
    rw [show counter.length + (addRaw counter [] true).length + 2 +
          (2 * (addRaw counter [] true).length + 3)
        = (2 * (addRaw counter [] true).length + 3) +
          (counter.length + (addRaw counter [] true).length + 2) from by ring,
      Function.iterate_add_apply, hrun1, hrun2]
    simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    funext k
    simp only [Function.update]
    split_ifs <;> simp_all

/-- `scanInput`'s full multi-bit loop: `prologue_step_scanInput_some` (pop one bit) then
    `prologue_process_bit_run` (its increment/emit), repeated until `Kg.io` is exhausted, landing
    at `.writeLength` with `prologueCounter` holding `base + bits.length`'s digits and `Kg.mem`
    gaining `bitLogRev bits base`'s entries — `bitLogRev`'s own recursion (`base+1`'s entries
    prepended, then the current bit's own entry appended) matches how `Function.update` layers
    each bit's write onto whatever the recursive call already produced. This is the scanning
    `Stmt` tree part of the construction described in this module's docstring. The
    trailing `MemSym.entryEnd` push is `scanInput`'s own unconditional terminator for the
    eventual length entry, folded in here rather than split into its own lemma since it happens
    exactly once, at the loop's exit. -/
lemma prologue_scanInput_run (hAgrees : PrologueAgrees p M) (bits : List Bool) (base : ℕ)
    (m0 : List MemSym) (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hIo : Sg Kg.io = bits)
    (hCounter : Sg (Kg.scratch .prologueCounter) = natToDigits base)
    (hWork : Sg (Kg.scratch .prologueWork) = ([] : List Digit))
    (hMem : Sg Kg.mem = m0) :
    ∃ n var', (flipBindPrologue p M)^[n] (some ⟨some (Λg.prologue .scanInput), var, Sg⟩)
      = some ⟨some (Λg.prologue .writeLength), var',
          Function.update
            (Function.update
              (Function.update Sg Kg.io [])
              (Kg.scratch .prologueCounter) (natToDigits (base + bits.length)))
            Kg.mem (MemSym.entryEnd :: (encodeLog (bitLogRev bits base) ++ m0))⟩ ∧
      n ≤ bits.length * (4 * bitLen (base + bits.length) + 10) + 1 := by
  induction bits generalizing base var Sg m0 with
  | nil =>
    refine ⟨1, { var with prologue := ⟨none, none⟩ }, ?_, by simp⟩
    simp only [List.length_nil, Nat.add_zero, bitLogRev, encodeLog, List.map_nil,
      List.flatten_nil, List.nil_append, Function.iterate_one]
    rw [prologue_step_scanInput_nil hAgrees var Sg hIo,
      update_self_of_eq Sg Kg.io [] hIo,
      update_self_of_eq Sg (Kg.scratch .prologueCounter) (natToDigits base) hCounter, hMem]
  | cons b rest ih =>
    have hstep := prologue_step_scanInput_some hAgrees b rest var Sg hIo
    have hB1 : (natToDigits base).length ≤ bitLen (base + (b :: rest).length) :=
      (natToDigits_length_le_bitLen base).trans (bitLen_le_of_le (by omega))
    have hB2 : (natToDigits (base + 1)).length ≤ bitLen (base + (b :: rest).length) :=
      (natToDigits_length_le_bitLen (base + 1)).trans
        (bitLen_le_of_le (by simp only [List.length_cons]; omega))
    cases b with
    | false =>
      obtain ⟨var1, hrun1⟩ := prologue_process_bit_run hAgrees (natToDigits base) false m0
        { var with prologue := ⟨some false, none⟩ }
        (Function.update Sg Kg.io rest) (by simp [hCounter]) (by simp [hWork]) (by simp [hMem])
        (by simp)
      rw [addRaw_natToDigits_succ] at hrun1
      simp only [Bool.false_eq_true, reduceIte] at hrun1
      obtain ⟨n2, var2, hrun2, hn2⟩ := ih (base + 1) m0 var1
        (Function.update
          (Function.update (Function.update Sg Kg.io rest)
            (Kg.scratch .prologueCounter) (natToDigits (base + 1)))
          (Kg.scratch .prologueWork) [])
        (by simp) (by simp) (by simp) (by simp [hMem])
      refine ⟨(n2 + ((natToDigits base).length + (natToDigits (base + 1)).length + 2)) + 1,
        var2, ?_, ?_⟩
      · have hlen : base + 1 + rest.length = base + (false :: rest).length := by
          simp only [List.length_cons]; omega
        have hlog : bitLogRev rest (base + 1) = bitLogRev (false :: rest) base := by
          simp [bitLogRev]
        rw [Function.iterate_succ_apply, hstep, Function.iterate_add_apply, hrun1, hrun2, hlen,
          hlog]
        simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        funext k
        simp only [Function.update]
        split_ifs <;> subst_vars <;> simp_all
      · have hlen : base + 1 + rest.length = base + (false :: rest).length := by
          simp only [List.length_cons]; omega
        rw [hlen] at hn2
        simp only [List.length_cons] at hB1 hB2 hn2 ⊢
        have hdist : (rest.length + 1) * (4 * bitLen (base + (rest.length + 1)) + 10) =
            rest.length * (4 * bitLen (base + (rest.length + 1)) + 10) +
              (4 * bitLen (base + (rest.length + 1)) + 10) := by ring
        omega
    | true =>
      obtain ⟨var1, hrun1⟩ := prologue_process_bit_run hAgrees (natToDigits base) true m0
        { var with prologue := ⟨some true, none⟩ }
        (Function.update Sg Kg.io rest) (by simp [hCounter]) (by simp [hWork]) (by simp [hMem])
        (by simp)
      rw [addRaw_natToDigits_succ] at hrun1
      simp only [reduceIte] at hrun1
      obtain ⟨n2, var2, hrun2, hn2⟩ := ih (base + 1)
        ((natToDigits (base + 1)).reverse.map MemSym.digit ++
          (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: m0))
        var1
        (Function.update
          (Function.update
            (Function.update (Function.update Sg Kg.io rest) Kg.mem
              ((natToDigits (base + 1)).reverse.map MemSym.digit ++
                (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: m0)))
            (Kg.scratch .prologueCounter) (natToDigits (base + 1)))
          (Kg.scratch .prologueWork) [])
        (by simp) (by simp) (by simp) (by simp)
      refine ⟨(n2 + ((natToDigits base).length + (natToDigits (base + 1)).length + 2 +
        (2 * (natToDigits (base + 1)).length + 3))) + 1, var2, ?_, ?_⟩
      · have hlen : base + 1 + rest.length = base + (true :: rest).length := by
          simp only [List.length_cons]; omega
        have hnat1 : natToDigits 1 = [(1 : Digit)] := by decide
        have hlog : encodeLog (bitLogRev rest (base + 1)) ++
            ((natToDigits (base + 1)).reverse.map MemSym.digit ++
              (MemSym.addrEnd :: MemSym.digit 1 :: MemSym.entryEnd :: m0)) =
            encodeLog (bitLogRev (true :: rest) base) ++ m0 := by
          show _ = encodeLog (bitLogRev rest (base + 1) ++ [(base + 1, 1)]) ++ m0
          rw [encodeLog_append, List.append_assoc]
          congr 1
          show _ = encodeLog [(base + 1, 1)] ++ m0
          simp [encodeLog, encodeEntry, hnat1]
        rw [Function.iterate_succ_apply, hstep, Function.iterate_add_apply, hrun1, hrun2, hlen]
        simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        funext k
        simp only [Function.update]
        split_ifs <;> subst_vars <;> simp_all
      · have hlen : base + 1 + rest.length = base + (true :: rest).length := by
          simp only [List.length_cons]; omega
        rw [hlen] at hn2
        simp only [List.length_cons] at hB1 hB2 hn2 ⊢
        have hdist : (rest.length + 1) * (4 * bitLen (base + (rest.length + 1)) + 10) =
            rest.length * (4 * bitLen (base + (rest.length + 1)) + 10) +
              (4 * bitLen (base + (rest.length + 1)) + 10) := by ring
        omega

/-- The prologue's full correctness theorem: starting at `.scanInput` with the raw
    `Bits` input on `Kg.io` and the `prologueCounter`, `prologueWork`, and `Kg.mem` stacks empty,
    the prologue runs to the RAM's entry point `entryAt p 0` with `AllInstrState.canonical` and
    `Kg.mem` equal to `encodeLog (inputLogRev bits)` — together with `lookupD_inputLogRev`, exactly
    the memory half of `Represents (compiledInputRAM p bits)` this boundary needs to establish
    (the register half is `compiledInputRAM`'s `emptyBank`, untouched by the prologue and so a
    separate, trivial obligation on whatever machine-start convention feeds this lemma). Composes
    `prologue_scanInput_run` (the bit-scan loop) with `prologue_writeLength_run` (draining the
    final bit-count into the length entry) and `prologue_step_done` (the bridge into `p`). -/
lemma prologue_run (hAgrees : PrologueAgrees p M) (bits : List Bool)
    (var : AllInstrState) (Sg : ∀ k, List (Γg p k))
    (hIo : Sg Kg.io = bits)
    (hCounter : Sg (Kg.scratch .prologueCounter) = ([] : List Digit))
    (hWork : Sg (Kg.scratch .prologueWork) = ([] : List Digit))
    (hMem : Sg Kg.mem = ([] : List MemSym)) :
    ∃ n, (flipBindPrologue p M)^[n] (some ⟨some (Λg.prologue .scanInput), var, Sg⟩)
      = some ⟨some (entryAt p 0), AllInstrState.canonical,
          Function.update
            (Function.update
              (Function.update (Function.update Sg Kg.io []) (Kg.scratch .prologueCounter) [])
              (Kg.scratch .prologueWork) [])
            Kg.mem (encodeLog (inputLogRev bits))⟩ ∧
      n ≤ bitLen bits.length + bits.length * (4 * bitLen bits.length + 10) + 3 := by
  obtain ⟨n1, var1, hrun1, hn1⟩ := prologue_scanInput_run hAgrees bits 0 [] var Sg hIo
    (by rw [natToDigits_zero]; exact hCounter) hWork hMem
  simp only [Nat.zero_add] at hrun1 hn1
  have hrun2 := prologue_writeLength_run hAgrees (natToDigits bits.length)
    (MemSym.entryEnd :: (encodeLog (bitLogRev bits 0) ++ ([] : List MemSym))) var1
    (Function.update
      (Function.update (Function.update Sg Kg.io []) (Kg.scratch .prologueCounter)
        (natToDigits bits.length))
      Kg.mem (MemSym.entryEnd :: (encodeLog (bitLogRev bits 0) ++ ([] : List MemSym))))
    (by simp) (by simp)
  have hstep := prologue_step_done hAgrees
    ({ var1 with prologue := { var1.prologue with digit := none } })
    (Function.update
      (Function.update
        (Function.update
          (Function.update (Function.update Sg Kg.io []) (Kg.scratch .prologueCounter)
            (natToDigits bits.length))
          Kg.mem (MemSym.entryEnd :: (encodeLog (bitLogRev bits 0) ++ ([] : List MemSym))))
        (Kg.scratch .prologueCounter) [])
      Kg.mem
      (MemSym.addrEnd :: ((natToDigits bits.length).reverse.map MemSym.digit ++
        (MemSym.entryEnd :: (encodeLog (bitLogRev bits 0) ++ ([] : List MemSym))))))
  refine ⟨((natToDigits bits.length).length + 1 + n1) + 1, ?_, ?_⟩
  · have hmemeq : MemSym.addrEnd :: ((natToDigits bits.length).reverse.map MemSym.digit ++
        (MemSym.entryEnd :: (encodeLog (bitLogRev bits 0) ++ ([] : List MemSym)))) =
      encodeLog (inputLogRev bits) := by
      unfold inputLogRev encodeLog
      simp only [List.map_cons, List.flatten_cons]
      unfold encodeEntry
      rw [natToDigits_zero]
      simp
    rw [Function.iterate_succ_apply', Function.iterate_add_apply, hrun1, hrun2, hstep]
    simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
    clear hrun1 hstep hrun2
    funext k
    simp only [Function.update]
    split_ifs <;> subst_vars <;> first | (simp_all; done) | (exfalso; simp_all)
  · have hlenle : (natToDigits bits.length).length ≤ bitLen bits.length :=
      natToDigits_length_le_bitLen bits.length
    omega

end NPComplete.RAMToTM.Generic
