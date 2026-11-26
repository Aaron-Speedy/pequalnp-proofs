import Normalize4928
import PEqualNP.Outside.L_meta_6371
open PEqualNP.CircuitLowerBounds LocalFano4126 Local4928
namespace Threshold4928
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
def ok (op : GateOp) := match op with | .and | .or => true | _ => false
lemma okSound (op : GateOp) (h : ok op = true) : op = .and ∨ op = .or := by cases op <;> simp_all [ok]
def C28 : Circuit := ⟨[⟨.or,[7,11]⟩, ⟨.or,[14,13]⟩, ⟨.and,[0,15]⟩, ⟨.or,[7,8]⟩, ⟨.or,[17,12]⟩, ⟨.and,[1,18]⟩, ⟨.or,[8,9]⟩, ⟨.or,[20,13]⟩, ⟨.or,[7,9]⟩, ⟨.or,[22,10]⟩, ⟨.and,[3,23]⟩, ⟨.or,[8,10]⟩, ⟨.or,[25,11]⟩, ⟨.and,[4,26]⟩, ⟨.or,[9,11]⟩, ⟨.or,[28,12]⟩, ⟨.and,[5,29]⟩, ⟨.or,[10,12]⟩, ⟨.or,[31,13]⟩, ⟨.and,[6,32]⟩, ⟨.or,[16,19]⟩, ⟨.or,[34,24]⟩, ⟨.or,[35,27]⟩, ⟨.or,[36,30]⟩, ⟨.or,[37,33]⟩, ⟨.or,[38,2]⟩, ⟨.or,[38,21]⟩, ⟨.and,[39,40]⟩],41⟩
theorem spec28 : ∀ t : Fin C28.gates.length, let g := C28.gates.get t; let a := g.inputs.getD 0 0; let b := g.inputs.getD 1 0;
    ok g.op = true ∧ g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+t.val ∧ b < 14+t.val := by decide +kernel
theorem legal28 : Legal C28 := by
  intro j g h
  obtain ⟨hj,he⟩ := List.getElem?_eq_some_iff.mp h
  let t : Fin C28.gates.length := ⟨j,hj⟩
  obtain ⟨op,rest⟩ := spec28 t
  subst g
  refine ⟨?_,_,_,rest⟩
  change (C28.gates[j]).op = .and ∨ (C28.gates[j]).op = .or
  change ok (C28.gates[j]).op = true at op
  exact okSound _ op
theorem computes28 (x : Fin 14 → Bool) : C28.eval (List.ofFn x) = true ↔ F x := by
  apply exactOf C28 legal28 _ _ x
  · unfold Pos; decide +kernel
  · intro y off maximal
    obtain ⟨j,rfl⟩ := PEqualNP.Outside.L_meta_6371 y off maximal
    clear off maximal
    revert j
    decide +kernel
theorem cost28 : C28.size = 28 := rfl
theorem marks28 : ∀ p l : Fin 7, Both C28 p l ↔ p ≠ 2 := by decide +kernel
def C29 : Circuit := ⟨[⟨.or,[11,13]⟩, ⟨.and,[0,14]⟩, ⟨.or,[7,8]⟩, ⟨.or,[16,12]⟩, ⟨.and,[1,17]⟩, ⟨.or,[8,9]⟩, ⟨.or,[19,13]⟩, ⟨.and,[2,20]⟩, ⟨.or,[7,9]⟩, ⟨.or,[22,10]⟩, ⟨.and,[3,23]⟩, ⟨.or,[8,10]⟩, ⟨.or,[25,11]⟩, ⟨.and,[4,26]⟩, ⟨.or,[9,11]⟩, ⟨.or,[28,12]⟩, ⟨.and,[5,29]⟩, ⟨.or,[10,12]⟩, ⟨.or,[31,13]⟩, ⟨.and,[6,32]⟩, ⟨.or,[15,18]⟩, ⟨.or,[34,21]⟩, ⟨.or,[35,24]⟩, ⟨.or,[36,27]⟩, ⟨.or,[37,30]⟩, ⟨.or,[38,33]⟩, ⟨.or,[39,0]⟩, ⟨.or,[39,7]⟩, ⟨.and,[40,41]⟩],42⟩
theorem spec29 : ∀ t : Fin C29.gates.length, let g := C29.gates.get t; let a := g.inputs.getD 0 0; let b := g.inputs.getD 1 0;
    ok g.op = true ∧ g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+t.val ∧ b < 14+t.val := by decide +kernel
theorem legal29 : Legal C29 := by
  intro j g h
  obtain ⟨hj,he⟩ := List.getElem?_eq_some_iff.mp h
  let t : Fin C29.gates.length := ⟨j,hj⟩
  obtain ⟨op,rest⟩ := spec29 t
  subst g
  refine ⟨?_,_,_,rest⟩
  change (C29.gates[j]).op = .and ∨ (C29.gates[j]).op = .or
  change ok (C29.gates[j]).op = true at op
  exact okSound _ op
theorem computes29 (x : Fin 14 → Bool) : C29.eval (List.ofFn x) = true ↔ F x := by
  apply exactOf C29 legal29 _ _ x
  · unfold Pos; decide +kernel
  · intro y off maximal
    obtain ⟨j,rfl⟩ := PEqualNP.Outside.L_meta_6371 y off maximal
    clear off maximal
    revert j
    decide +kernel
theorem cost29 : C29.size = 29 := rfl
theorem marks29 : ∀ p l : Fin 7, Both C29 p l ↔ True := by decide +kernel
end Threshold4928
#print axioms Threshold4928.computes28
#print axioms Threshold4928.marks28
#print axioms Threshold4928.computes29
#print axioms Threshold4928.marks29
