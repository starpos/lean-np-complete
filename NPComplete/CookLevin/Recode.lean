module

public import NPComplete.CookLevin.TM0
public import NPComplete.CookLevin.Machines.TM2to1.PackSim
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.Encoding

/-!
`TM0ComputableInPolyTime` for `InP` uses an `Option Bool` tape. The TM2→TM1→TM0
drop produces a multiplexed `Γ'` tape. A fixed-width block encoding of `Γ'`
lets the same function run on `Option Bool` without rewriting the translators.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Computability (encodeBool)
open Polynomial
open scoped Polynomial

/-- Fixed-width Boolean encoding of a finite inhabited alphabet. -/
structure BlockEnc (Γ : Type*) [Inhabited Γ] [Finite Γ] where
  n : ℕ
  enc : Γ → List.Vector Bool n
  dec : List.Vector Bool n → Γ
  enc_default : enc default = List.Vector.replicate n false
  dec_enc : ∀ a, dec (enc a) = a

noncomputable def BlockEnc.ofFinite (Γ : Type*) [Inhabited Γ] [Finite Γ] : BlockEnc Γ :=
  have h := TM1to1.exists_enc_dec (Γ := Γ)
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.choose_spec.2⟩

def BlockEnc.encodeList {Γ : Type*} [Inhabited Γ] [Finite Γ] (e : BlockEnc Γ)
    (l : List Γ) : List Bool :=
  l.flatMap fun a => (e.enc a).toList

lemma BlockEnc.encodeList_length {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (l : List Γ) :
    (e.encodeList l).length = l.length * e.n := by
  induction l with
  | nil => simp [encodeList]
  | cons _ l ih =>
    simp [encodeList, List.flatMap_cons, List.Vector.toList_length]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

lemma BlockEnc.encodeList_cons {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (a : Γ) (l : List Γ) :
    e.encodeList (a :: l) = (e.enc a).toList ++ e.encodeList l := by
  simp [encodeList]

lemma BlockEnc.encodeList_nil {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) : e.encodeList [] = [] :=
  rfl

/-- Split a bit string into `n`-bit symbols. Incomplete tail chunks are dropped. -/
def BlockEnc.decodeList {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (l : List Bool) : List Γ :=
  if h : e.n = 0 ∨ l.length < e.n then
    []
  else
    have hc : (l.take e.n).length = e.n := by
      simp [List.length_take]
      omega
    e.dec (⟨l.take e.n, hc⟩ : List.Vector Bool e.n) :: e.decodeList (l.drop e.n)
termination_by l.length
decreasing_by
  simp [List.length_drop]
  omega

lemma BlockEnc.decodeList_of_short {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) {l : List Bool} (h : e.n = 0 ∨ l.length < e.n) :
    e.decodeList l = [] := by
  unfold decodeList
  simp [h]

lemma BlockEnc.decodeList_nil {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) : e.decodeList [] = [] := by
  refine decodeList_of_short e ?_
  by_cases h : e.n = 0
  · exact Or.inl h
  · exact Or.inr (Nat.pos_of_ne_zero h)

lemma BlockEnc.decodeList_append_block {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (hn : 0 < e.n) (v : List.Vector Bool e.n) (rest : List Bool) :
    e.decodeList (v.toList ++ rest) = e.dec v :: e.decodeList rest := by
  have hlen : ¬ (e.n = 0 ∨ (v.toList ++ rest).length < e.n) := by
    simp [List.Vector.toList_length]
    omega
  have htake : (v.toList ++ rest).take e.n = v.toList :=
    List.take_left' (List.Vector.toList_length v)
  have hdrop : (v.toList ++ rest).drop e.n = rest :=
    List.drop_left' (List.Vector.toList_length v)
  conv_lhs => unfold decodeList
  rw [dite_eq_right hlen]
  dsimp
  refine congr_arg₂ (· :: ·) ?_ (congrArg e.decodeList hdrop)
  apply congrArg e.dec
  exact Subtype.ext htake

lemma BlockEnc.decode_encodeList_cons {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (hn : 0 < e.n) (a : Γ) (l : List Γ) :
    e.decodeList (e.encodeList (a :: l)) = a :: e.decodeList (e.encodeList l) := by
  rw [encodeList_cons, decodeList_append_block e hn, e.dec_enc]

lemma BlockEnc.decode_encodeList {Γ : Type*} [Inhabited Γ] [Finite Γ]
    (e : BlockEnc Γ) (hn : 0 < e.n) (l : List Γ) :
    e.decodeList (e.encodeList l) = l := by
  induction l with
  | nil => simp [encodeList_nil, decodeList_nil]
  | cons a l ih =>
    rw [decode_encodeList_cons e hn, ih]

/-- The Boolean encoding of a TM2 input after packaging and `trInit`.
    Written as the reverse-block expansion so the expander TM can match it. -/
noncomputable def encodePackedInput (tm : FinTM2)
    (inp : tm.Γ tm.k₀ ≃ Bool) (l : List Bool) : List Bool :=
  let eΓ := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  let cell (isBottom : Bool) (x : Bool) : TM2to1.Γ' tm.K (TM2to1.PackΓ tm) :=
    (isBottom, Function.update (fun _ => none) tm.k₀
      (some ⟨inp.symm x, TM2to1.mem_usedSymbols_k₀ tm _⟩))
  match l.reverse with
  | [] => (eΓ.enc ((true, fun _ => none) : TM2to1.Γ' _ _)).toList
  | b :: rest =>
      (eΓ.enc (cell true b)).toList ++
        rest.flatMap fun x => (eΓ.enc (cell false x)).toList

/-- Recover the output bit sitting in the `k₁` slot of the bottom `Γ'` cell. -/
noncomputable def decodePackedOutput (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) (l : List Bool) : List Bool :=
  let eΓ := BlockEnc.ofFinite (TM2to1.Γ' tm.K (TM2to1.PackΓ tm))
  let bits := (l ++ List.replicate eΓ.n false).take eΓ.n
  if h : bits.length = eΓ.n then
    match (eΓ.dec ⟨bits, h⟩).2 tm.k₁ with
    | some x => encodeBool (out x.1)
    | none => encodeBool false
  else
    encodeBool false

lemma tm2_supportsStmt_univ {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    [Fintype Λ] (q : TM2.Stmt Γ Λ σ) : TM2.SupportsStmt Finset.univ q := by
  induction q with
  | goto l => intro; exact Finset.mem_univ _
  | branch _ _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | halt => trivial
  | push _ _ _ ih => exact ih
  | peek _ _ _ ih => exact ih
  | pop _ _ _ ih => exact ih
  | load _ _ ih => exact ih

lemma tm2_univ_supports {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    [Inhabited Λ] [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) :
    TM2.Supports M Finset.univ :=
  ⟨Finset.mem_univ _, fun _ _ => tm2_supportsStmt_univ _⟩

/-- Existing `tr`, with states restricted to `trSupp` of the packed program. -/
noncomputable def packedTM0 (tm : FinTM2) : TM1to0.FinTM0 :=
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  letI : Inhabited (TM2to1.packFinTM2 tm).Λ := ⟨(TM2to1.packFinTM2 tm).main⟩
  letI : Fintype (TM2to1.packFinTM2 tm).Λ := tm.ΛFin
  TM1to0.ofTM1 (TM2to1.packTr tm)
    (TM2to1.trSupp (TM2to1.packFinTM2 tm).m Finset.univ)
    (TM2to1.tr_supports (TM2to1.packFinTM2 tm).m (tm2_univ_supports _))

/-- Polynomial wrapper: keep the concrete degree off the kernel. -/
noncomputable def recodeTimeG (p : Polynomial ℕ) (c : ℕ) : Polynomial ℕ :=
  p * C c * (2 * (X + p * C c) + 4) * C c + X * C c + C c

noncomputable def recodeTime (p : Polynomial ℕ) (c : ℕ) : Polynomial ℕ :=
  recodeTimeG p c

lemma recodeTimeG_eval (p : Polynomial ℕ) (c n : ℕ) :
    (recodeTimeG p c).eval n =
      p.eval n * c * (2 * (n + p.eval n * c) + 4) * c + n * c + c := by
  simp [recodeTimeG, eval_add, eval_mul, eval_X]

end NPComplete.CookLevin
