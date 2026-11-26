import Graph9750NotCount
import PEqualNP.Outside.L_meta_9732
namespace PEqualNP.Outside.Signed9750
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9750_aux (f0)
def pairs12 : List (Fin 12 × Fin 12) := [(0, 7), (0, 11), (1, 6), (1, 10), (1, 11), (2, 9), (2, 10), (3, 8), (3, 9), (3, 11), (4, 7), (4, 8), (4, 10), (5, 6), (5, 7), (5, 9)]

theorem graphEdgeEq (x : Assignment) : f0 x = pairs12.any (fun e => x e.1 && x e.2) := by
  simp [f0,pairs12]
  all_goals ac_rfl

theorem someNegation (C : Circuit) (ok : FanInTwo C)
    (ev : ∀ x : Assignment, C.eval (List.ofFn x) = f0 x) (size : C.size ≤ 20) :
    1 ≤ notCount C.gates := by
  by_contra! under
  have n0 : notCount C.gates = 0 := by omega
  have no : C.gates.filter (fun g => !useBinary g) = [] := List.length_eq_zero_iff.mp n0
  apply PEqualNP.Outside.L_meta_9732
  refine ⟨C,?_,size,?_⟩
  · intro g hg
    obtain ⟨ops,arity⟩ := ok g hg
    refine ⟨?_,arity⟩
    have ne : g.op ≠ .not := by
      intro hn
      have bad : g ∈ C.gates.filter (fun h => !useBinary h) :=
        List.mem_filter.mpr ⟨hg,by simp [useBinary,hn]⟩
      simp [no] at bad
    simpa [ne] using ops
  · intro x
    rw [ev,graphEdgeEq,List.any_eq_true]
    have map_eq : ([(0, 7), (0, 11), (1, 6), (1, 10), (1, 11), (2, 9), (2, 10), (3, 8), (3, 9), (3, 11), (4, 7), (4, 8), (4, 10), (5, 6), (5, 7), (5, 9)] : List (ℕ × ℕ)) = pairs12.map (fun e => (e.1.val,e.2.val)) := by decide
    rw [map_eq]
    constructor
    · rintro ⟨⟨u,v⟩,hm,on⟩
      exact ⟨u,v,List.mem_map.mpr ⟨(u,v),hm,rfl⟩,Bool.and_eq_true_iff.mp on⟩
    · rintro ⟨u,v,hm,hu,hv⟩
      obtain ⟨⟨a,b⟩,hab,eq⟩ := List.mem_map.mp hm
      have au : a = u := Fin.ext (congrArg Prod.fst eq)
      have bv : b = v := Fin.ext (congrArg Prod.snd eq)
      subst a; subst b
      exact ⟨(u,v),hab,by simp [hu,hv]⟩

theorem negationRange (C : Circuit) (ok : FanInTwo C)
    (ev : ∀ x : Assignment, C.eval (List.ofFn x) = f0 x) (size : C.size ≤ 20) :
    1 ≤ notCount C.gates ∧ notCount C.gates ≤ 6 :=
  ⟨someNegation C ok ev size,fewNegations C ok ev size⟩
end PEqualNP.Outside.Signed9750
#print axioms PEqualNP.Outside.Signed9750.negationRange
