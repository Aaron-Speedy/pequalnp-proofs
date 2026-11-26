import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.Graph9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def edges : List (Fin 25 × Fin 25) := [(0,16),(0,22),(0,24),(1,13),(1,17),(1,23),(2,13),(2,14),(2,18),(2,24),(3,14),(3,15),(3,19),(4,13),(4,15),(4,16),(4,20),(5,14),(5,16),(5,17),(5,21),(6,15),(6,17),(6,18),(6,22),(7,16),(7,18),(7,19),(7,23),(8,17),(8,19),(8,20),(8,24),(9,18),(9,20),(9,21),(10,13),(10,19),(10,21),(10,22),(11,14),(11,20),(11,22),(11,23),(12,15),(12,21),(12,23),(12,24)]
def original : List (ℕ × ℕ) := [(0,16),(0,22),(0,24),(1,13),(1,17),(1,23),(2,13),(2,14),(2,18),(2,24),(3,14),(3,15),(3,19),(4,13),(4,15),(4,16),(4,20),(5,14),(5,16),(5,17),(5,21),(6,15),(6,17),(6,18),(6,22),(7,16),(7,18),(7,19),(7,23),(8,17),(8,19),(8,20),(8,24),(9,18),(9,20),(9,21),(10,13),(10,19),(10,21),(10,22),(11,14),(11,20),(11,22),(11,23),(12,15),(12,21),(12,23),(12,24)]
def C : Circuit := ⟨[⟨.or,[1,2]⟩,
⟨.or,[4,10]⟩,
⟨.or,[25,26]⟩,
⟨.and,[13,27]⟩,
⟨.or,[2,3]⟩,
⟨.or,[5,11]⟩,
⟨.or,[29,30]⟩,
⟨.and,[14,31]⟩,
⟨.or,[3,4]⟩,
⟨.or,[6,12]⟩,
⟨.or,[33,34]⟩,
⟨.and,[15,35]⟩,
⟨.or,[0,4]⟩,
⟨.or,[5,7]⟩,
⟨.or,[37,38]⟩,
⟨.and,[16,39]⟩,
⟨.or,[1,5]⟩,
⟨.or,[6,8]⟩,
⟨.or,[41,42]⟩,
⟨.and,[17,43]⟩,
⟨.or,[2,6]⟩,
⟨.or,[7,9]⟩,
⟨.or,[45,46]⟩,
⟨.and,[18,47]⟩,
⟨.or,[3,7]⟩,
⟨.or,[8,10]⟩,
⟨.or,[49,50]⟩,
⟨.and,[19,51]⟩,
⟨.or,[4,8]⟩,
⟨.or,[9,11]⟩,
⟨.or,[53,54]⟩,
⟨.and,[20,55]⟩,
⟨.or,[5,9]⟩,
⟨.or,[10,12]⟩,
⟨.or,[57,58]⟩,
⟨.and,[21,59]⟩,
⟨.or,[0,6]⟩,
⟨.or,[10,11]⟩,
⟨.or,[61,62]⟩,
⟨.and,[22,63]⟩,
⟨.or,[1,7]⟩,
⟨.or,[11,12]⟩,
⟨.or,[65,66]⟩,
⟨.and,[23,67]⟩,
⟨.or,[0,2]⟩,
⟨.or,[8,12]⟩,
⟨.or,[69,70]⟩,
⟨.and,[24,71]⟩,
⟨.or,[28,32]⟩,
⟨.or,[36,40]⟩,
⟨.or,[44,48]⟩,
⟨.or,[52,56]⟩,
⟨.or,[60,64]⟩,
⟨.or,[68,72]⟩,
⟨.or,[73,74]⟩,
⟨.or,[75,76]⟩,
⟨.or,[77,78]⟩,
⟨.or,[79,80]⟩,
⟨.or,[82,81]⟩],83⟩
theorem size : C.size = 59 := by decide
theorem mono : Monotone2 C := by simp [Monotone2,C]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 3000000 in
theorem evalStars (x : Fin 25 → Bool) : C.eval (List.ofFn x) =
    edges.any (fun p => x p.1 && x p.2) := by
  simp [C,edges,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD,
    Bool.and_or_distrib_left,Bool.or_and_distrib_right,Bool.or_assoc]
  all_goals ac_rfl

theorem exactEdges (x : Fin 25 → Bool) : C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 25, (u.val,v.val) ∈ original ∧ x u = true ∧ x v = true := by
  have mapEq : edges.map (fun p => (p.1.val,p.2.val)) = original := by decide
  rw [evalStars,List.any_eq_true]
  constructor
  · rintro ⟨⟨u,v⟩,h,p⟩
    exact ⟨u,v,mapEq ▸ List.mem_map.mpr ⟨(u,v),h,rfl⟩,Bool.and_eq_true.mp p⟩
  · rintro ⟨u,v,h,p,q⟩
    rw [← mapEq] at h
    obtain ⟨⟨i,j⟩,mem,eq⟩ := List.mem_map.mp h
    have a : i = u := Fin.ext (congrArg Prod.fst eq)
    have b : j = v := Fin.ext (congrArg Prod.snd eq)
    exact ⟨(i,j),mem,by simp [a,b,p,q]⟩
end PEqualNP.Outside.Graph9738
#print axioms PEqualNP.Outside.Graph9738.exactEdges
