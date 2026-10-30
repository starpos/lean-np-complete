module

public import NPComplete

@[expose] public section

namespace NPCompleteTest.Resources

open NPComplete.BoundedWhile NPComplete.RAMToTM NPComplete.CookLevin NPComplete.BitEncoding

def loopProg : Program := .forN (.reg 0) .skip

lemma loopBound (x : Bits) : ProgramBoundedIn 0 (bitInputStore x) loopProg := by
  simp [loopProg, ProgramBoundedIn, ExprBoundedIn]

noncomputable def loopDecider : BoundedWhileDecider (fun x : Bits => x) (fun _ => True)
    (fun x => loopProg.eval (bitInputStore x) 0 = 1) :=
  BoundedWhileDecider.ofProgramBoundedIn id loopProg 0 (fun _ => 0) 0 (by simp)
    (by simp [loopProg, ScanFree]) loopBound

def setProg : Program := .assign 0 (.const 0)

lemma setBound (x : Bits) : ProgramBoundedIn 0 (bitInputStore x) setProg := by
  simp [setProg, ProgramBoundedIn, ExprBoundedIn]

noncomputable def setDecider : BoundedWhileDecider (fun x : Bits => x) (fun _ => True)
    (fun x => setProg.eval (bitInputStore x) 0 = 1) :=
  BoundedWhileDecider.ofProgramBoundedIn id setProg 0 (fun _ => 0) 0 (by simp)
    (by simp [setProg, ScanFree]) setBound

noncomputable def preludeDecider : BoundedWhileDecider
    (fun aw : Bits × Bits => pairBits aw.1 aw.2) (fun _ => True) (fun _ => False) :=
  pairPreludeDecider id (fun _ _ => False) setProg 0 (fun _ => 0) 0 (by simp)
    (by simp [setProg, ScanFree]) (by intro a w; simp [setProg, ProgramBoundedIn, ExprBoundedIn])
    (by intro a w; simp [setProg, eval_assign, writeReg_same, Expr.eval])

end NPCompleteTest.Resources
