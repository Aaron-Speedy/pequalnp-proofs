import CircuitAPart26
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_16977_aux
namespace S_25
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_160 : ∀ i, 160 ≤ i → i < 168 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_168 : ∀ i, 168 ≤ i → i < 170 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 168 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 170 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (z7_168)))))))))))))))))))))

end S_25

end PEqualNP.Outside.L_meta_16977_aux
