import CircuitAPart11
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_16977_aux
namespace S_13
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := z5_0

end S_13

end PEqualNP.Outside.L_meta_16977_aux
