import MarkedData5208
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

end Marked5208
#print axioms Marked5208.geometry_ok
#print axioms Marked5208.wellFormed
