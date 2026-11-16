module

public import NPComplete.CookLevin.Verifier.ThreeCNFEvalOuterBounded
public import NPComplete.CookLevin.Verifier.ThreeCNFEvalTop
public import NPComplete.CookLevin.UniformPackaging.DecoderBounds

/-!
# Top-level ThreeCNF evaluator storage bounds

The numbered storage-bounds chain this module held is superseded by the layout
version of the ThreeCNF resource composition (`ThreeCNFEvalStages.lean`), which
the top wiring reads directly. The module stays as an import target for
downstream users.
-/

@[expose] public section

namespace NPComplete.CookLevin

end NPComplete.CookLevin
