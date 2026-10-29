module

import NPComplete.RAMToTM.Generic.Api.CompileExecBounded
import NPComplete.RAMToTM.Generic.Machine.DigitAdd

/-!
# The same from a plain `import`

Expected: `simp [f]` / `rw [f]` / `unfold f` FAIL for the mutual `compile` and the
well-founded `addRaw`; `f.eq_def` still works. The library has `compile_length` and similar
lemmas but no `compile_skip`-style equation lemmas, which limits the common downstream pattern
`simp [compile]` under a plain `import`.
-/

open NPComplete.RAMToTM NPComplete.BoundedWhile NPComplete.BitCostRAM

/-- compile._mutual -/
#guard_msgs (substring := true) in
example : compile .skip 0 0 = [] := by simp [compile]
/-- compile._mutual -/
#guard_msgs (substring := true) in
example : compile .skip 0 0 = [] := by simp only [compile]
/-- compile._mutual -/
#guard_msgs (substring := true) in
example : compile .skip 0 0 = [] := by unfold compile; rfl
/-- addRaw._unary -/
#guard_msgs (substring := true) in
example : addRaw [] [] false = [] := by simp [addRaw]
/-- `simp` made no progress -/
#guard_msgs (substring := true) in
example : addRaw [] [] false = [] := by rw [addRaw]; simp
/-- `simp` made no progress -/
#guard_msgs (substring := true) in
example : addRaw [] [] false = [] := by unfold addRaw; simp
-- expected ok: `eq_def`
example : addRaw [] [] false = [] := by rw [addRaw.eq_def]; simp
example : compile .skip 0 0 = [] := by rw [compile.eq_def]
-- expected ok: an existing library lemma about compile
example (p : Program) (pc sb : Nat) : (compile p pc sb).length = codeLenP p := compile_length p pc sb
