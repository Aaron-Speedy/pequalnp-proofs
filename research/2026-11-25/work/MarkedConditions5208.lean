import Marked5208
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
namespace Marked5208
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
attribute [local instance] lineDegreeGateOpDecEq

def pins (k : ℕ) (s : Fin 26) : Prop :=
  (gateAt C k).op = .and ∧ (26+k=C.output ∨ InCone 26 C k (C.output-26)) ∧
  gateVal 26 C k (pairInput 0 13) = true ∧
  ∀ b : Fin 2, wireVal 26 C (opnd C k b) (pairInput s s) = false

theorem geometry_ok : C.size = 66 ∧ InCone 26 C 4 9 ∧ pins 4 0 ∧ pins 9 13 ∧
    gateVal 26 C 4 (pairInput 13 13) = true ∧ C.eval (List.ofFn (pairInput (13 : Fin 26) 13)) = false := by
  unfold pins
  decide +kernel

theorem wellFormed (j : ℕ) (g : Gate) (h : C.gates[j]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j := by
  have cert : ∀ i : Fin C.gates.length,
      let t := C.gates[i.val]
      (t.op = .and ∨ t.op = .or) ∧ t.inputs.length = 2 ∧
      t.inputs[0]! ≠ t.inputs[1]! ∧ t.inputs[0]! < 26+i.val ∧ t.inputs[1]! < 26+i.val := by decide +kernel
  obtain ⟨hj,hg⟩ := List.getElem?_eq_some_iff.mp h
  subst g
  obtain ⟨ok,len,ne,a,b⟩ := cert ⟨j,hj⟩
  refine ⟨ok,_,_,?_,ne,a,b⟩
  generalize e : C.gates[j].inputs = l at *
  cases l with
  | nil => simp_all
  | cons u l =>
    cases l with
    | nil => simp_all
    | cons v rest =>
      have emp : rest = [] := by simpa using len
      subst rest
      rfl

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
