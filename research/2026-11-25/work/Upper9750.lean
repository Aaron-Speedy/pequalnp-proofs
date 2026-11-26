import Restriction9750
namespace PEqualNP.Outside.L_meta_9750_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def starCircuit : Circuit := ⟨[⟨.or,[7,11]⟩,
  ⟨.and,[0,12]⟩,
  ⟨.or,[6,10]⟩,
  ⟨.or,[14,11]⟩,
  ⟨.and,[1,15]⟩,
  ⟨.or,[9,10]⟩,
  ⟨.and,[2,17]⟩,
  ⟨.or,[8,9]⟩,
  ⟨.or,[19,11]⟩,
  ⟨.and,[3,20]⟩,
  ⟨.or,[7,8]⟩,
  ⟨.or,[22,10]⟩,
  ⟨.and,[4,23]⟩,
  ⟨.or,[6,7]⟩,
  ⟨.or,[25,9]⟩,
  ⟨.and,[5,26]⟩,
  ⟨.or,[13,16]⟩,
  ⟨.or,[28,18]⟩,
  ⟨.or,[29,21]⟩,
  ⟨.or,[30,24]⟩,
  ⟨.or,[31,27]⟩],32⟩
theorem starSize : starCircuit.size = 21 := by decide
theorem starMono : Monotone2 starCircuit := by simp [starCircuit,Monotone2]
set_option maxRecDepth 20000 in
theorem starEval (x : Fin 12 → Bool) : starCircuit.eval (List.ofFn x) = f0 x := by
  simp [starCircuit, Circuit.eval, Circuit.wires, GateOp.eval, f0,List.getD_eq_getElem?_getD,Bool.and_or_distrib_left,Bool.or_assoc]
  all_goals ac_rfl
end PEqualNP.Outside.L_meta_9750_aux
#print axioms PEqualNP.Outside.L_meta_9750_aux.starEval
