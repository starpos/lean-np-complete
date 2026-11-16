module

public import NPComplete.CookLevin.Verifier.CNFEvalOuterBounded

/-!
# Top-level evaluator storage bounds

The numbered storage-bounds chain this module held is superseded by the layout
version of the evaluator's resource composition (`CNFEvalStages.lean`), which the
stage contracts read directly. The module stays as an import target for
downstream users.
-/

@[expose] public section

namespace NPComplete.CookLevin

end NPComplete.CookLevin
