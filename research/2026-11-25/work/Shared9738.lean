import PEqualNP.Outside.L_meta_1500
import PolarLower9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.Plane9738
theorem bothSides (C : Circuit) (mono : Monotone2 C) (ok : GraphOK C) (small : C.size ≤ 58) :
    2 ≤ C.lineDeg 25 (marks 25) ∧ 2 ≤ C.lineDeg 25 (leftMarks 25) := by
  constructor
  · by_contra! h
    have hh : HasLineDegree 25 (marks 25) C 1 := by
      unfold HasLineDegree
      omega
    have bound := sharedLower PEqualNP.Outside.L_meta_1500 C mono ok hh
    omega
  · by_contra! h
    have hh : HasLineDegree 25 (leftMarks 25) C 1 := by
      unfold HasLineDegree
      omega
    have bound := sharedLeft PEqualNP.Outside.L_meta_1500 C mono ok hh
    omega
end PEqualNP.Outside.Plane9738
#print axioms PEqualNP.Outside.Plane9738.bothSides
