module

public import NPComplete.CookLevin.Recode.DecList.RawComputable

/-!
# Decoded-list polynomial bound

The block decoder's final tape must satisfy the polynomial-time interface, not
only establish a correct output. This module proves a bound for complete runs
and packages the decoder as polynomial-time computable.
-/

@[expose] public section

namespace NPComplete.CookLevin

open Turing
open Polynomial
open scoped Polynomial
open NPComplete.CookLevin.TM2to1
  (StepsTo stepsTo_zero stepsTo_cons stepsTo_succ stepsTo_trans)

noncomputable def decListRawComputableInPolyTime (tm : FinTM2)
    (out : tm.Γ tm.k₁ ≃ Bool) :
    TM0ComputableInPolyTime (fun l : List Bool => l) (fun l : List Bool => l)
      (decodePackedOutputList tm out) where
  toTM0ComputableAux := decListRawAux tm out
  time := decListRawTime (decListN tm)
  outputsFun raw := decListRawMachine_machineOutputsInTime tm out raw

end NPComplete.CookLevin
