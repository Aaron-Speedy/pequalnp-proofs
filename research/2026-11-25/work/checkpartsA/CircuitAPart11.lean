import CircuitAPart10
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_16977_aux
namespace S_13
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0

end S_13

end PEqualNP.Outside.L_meta_16977_aux
