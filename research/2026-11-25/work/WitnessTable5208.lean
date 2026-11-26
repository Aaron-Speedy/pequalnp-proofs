import Reflect5208
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
namespace Marked5208
open Reflection
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
def E (p l : Fin 13) : Term := {Fin.castAdd 13 p, Fin.natAdd 13 l}
def expected : DNF := (edges.map (fun q => E q.1 q.2)).toFinset ∪ {{0,13,14}}
theorem resultEq : result = expected := by decide +kernel
theorem lowerTerms : ∀ t ∈ result, ∃ p l : Fin 13, p-l ∈ D ∧ E p l ⊆ t := by rw [resultEq]; decide +kernel
theorem upperTerms : ∀ p l : Fin 13, p-l ∈ D → E p l ∈ result := by rw [resultEq]; decide +kernel
theorem semantic (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 13, p-l ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  rw [← evaluates]
  simp only [readD,decide_eq_true_eq]
  constructor
  · rintro ⟨t,ht,yes⟩
    obtain ⟨p,l,e,sub⟩ := lowerTerms t ht
    exact ⟨p,l,e,yes _ (sub (by simp [E])),yes _ (sub (by simp [E]))⟩
  · rintro ⟨p,l,e,hp,hl⟩
    refine ⟨_,upperTerms p l e,?_⟩
    intro i hi
    rcases (show i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l by simpa [E] using hi) with rfl | rfl
    · exact hp
    · exact hl
theorem witness66 : (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧ ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧ x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;     x1.size ≤ (66 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x4 x10 x11 ∧ x9 x10 x6 ∧ x9 x11 x7) := by
  refine ⟨C,?_⟩
  dsimp only
  obtain ⟨sz,cone,early,late,dirty,off⟩ := geometry_ok
  exact ⟨sz.le,wellFormed,semantic,
    ⟨4,by decide,early.1,pairInput 13 13,dirty,off⟩,
    4,9,cone,early,late⟩

end Marked5208
#print axioms Marked5208.geometry_ok
#print axioms Marked5208.wellFormed
#print axioms Marked5208.witness66
