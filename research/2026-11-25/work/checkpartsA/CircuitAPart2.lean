import CircuitAPart1
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_16977_aux
namespace S_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0

end S_0

end PEqualNP.Outside.L_meta_16977_aux
