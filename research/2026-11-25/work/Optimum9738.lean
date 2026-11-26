import Shared9738
import StarFast9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.Plane9738
def linearOnOneSide (C : Circuit) := HasLineDegree 25 (marks 25) C 1 ∨ HasLineDegree 25 (leftMarks 25) C 1
theorem exactMinimum (s : ℕ) :
    (∃ C : Circuit, Monotone2 C ∧ GraphOK C ∧ linearOnOneSide C ∧ C.size ≤ s) ↔ 59 ≤ s := by
  constructor
  · rintro ⟨C,m,ok,deg,bd⟩
    rcases deg with h|h
    · exact (sharedLower PEqualNP.Outside.L_meta_1500 C m ok h).trans bd
    · exact (sharedLeft PEqualNP.Outside.L_meta_1500 C m ok h).trans bd
  · intro h
    refine ⟨Graph9738.C,Graph9738.mono,Graph9738.exactEdges,Or.inl ?_,by simpa only [Graph9738.size] using h⟩
    exact le_of_eq Graph9738.sideDegrees.2
theorem remainingCase : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 58 ∧ (∀ x : Fin 25 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 25, (u.val, v.val) ∈ ([(0, 16), (0, 22), (0, 24), (1, 13), (1, 17), (1, 23), (2, 13), (2, 14), (2, 18), (2, 24), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 17), (8, 19), (8, 20), (8, 24), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23), (12, 15), (12, 21), (12, 23), (12, 24)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)))) ↔
    ¬ ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 58 ∧ GraphOK C ∧
      2 ≤ C.lineDeg 25 (marks 25) ∧ 2 ≤ C.lineDeg 25 (leftMarks 25) := by
  constructor
  · rintro h ⟨C,m,sz,ok,_⟩
    exact h ⟨C,m,sz,ok⟩
  · rintro h ⟨C,m,sz,ok⟩
    exact h ⟨C,m,sz,ok,bothSides C m ok sz⟩
end PEqualNP.Outside.Plane9738
#print axioms PEqualNP.Outside.Plane9738.exactMinimum
