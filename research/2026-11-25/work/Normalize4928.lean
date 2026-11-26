import Tree4126
import PEqualNP.Outside.L_meta_4926
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.SingleLevel
open LocalFano4126
namespace Local4928
abbrev Valid (C : Circuit) := C.size ≤ 27 ∧ Legal C ∧ ∀ x, C.eval (List.ofFn x) = true ↔ F x
abbrev Tree (C : Circuit) := ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
abbrev Both (C : Circuit) (p l : Fin 7) := 2 ≤ C.lineDeg 14 {p.val} ∧ 2 ≤ C.lineDeg 14 {7+l.val}
def Claim := ∀ C p l, Valid C → Incident p l → 2 ≤ C.lineDeg 14 {p.val} →
  2 ≤ C.lineDeg 14 {7+l.val} → 2 ≤ (andDepths C 14).getD C.output 0 → ¬ Tree C →
  ∃ D, Valid D ∧ Tree D ∧ Both D p l

theorem strictModel {C : Circuit} (h : Legal C) : PEqualNP.TopForm.IsAO2 14 C := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨j,hj⟩ := List.getElem?_of_mem hg
    exact (h j g hj).1
  · intro j hj i hi
    rw [PEqualNP.Outside.L_meta_4926.gateAt_eq hj] at hi
    obtain ⟨_,a,b,ins,_,earlier,later⟩ := h j C.gates[j] (List.getElem?_eq_getElem hj)
    rw [ins] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl <;> assumption
  · intro g hg
    obtain ⟨j,hj⟩ := List.getElem?_of_mem hg
    obtain ⟨_,a,b,ins,_⟩ := h j g hj
    simp [ins]

theorem noTree {C : Circuit} {p l : Fin 7} (val : Valid C) (inc : Incident p l)
    (both : Both C p l) : ¬Tree C := by
  intro tr
  obtain ⟨hp,hl⟩ := both
  rcases PEqualNP.Outside.L_meta_2225 C p l val tr inc with h|h
  · change C.lineDeg 14 {p.val} ≤ 1 at h; omega
  · change C.lineDeg 14 {7+l.val} ≤ 1 at h; omega

theorem equivalent : Claim ↔ ∀ C p l, Valid C → Incident p l → ¬ Both C p l := by
  constructor
  · intro claim C p l val inc both
    let v := Fin.castAdd 7 p
    have reject : C.eval (List.ofFn fun j : Fin 14 => decide (j=v)) = false := by
      apply Bool.eq_false_iff.mpr
      intro on
      obtain ⟨a,b,_,ha,hb⟩ := (val.2.2 _).mp on
      have eq : Fin.natAdd 7 b = v := of_decide_eq_true hb
      have e := congrArg Fin.val eq
      change 7 + b.val = p.val at e
      omega
    have depth := PEqualNP.Outside.L_meta_4926 14 C v (strictModel val.2.1) reject both.1
    obtain ⟨D,hd,tr,bd⟩ := claim C p l val inc both.1 both.2 depth (noTree val inc both)
    exact noTree hd inc bd tr
  · intro h C p l val inc hp hl _ _
    exact (h C p l val inc ⟨hp,hl⟩).elim
end Local4928
#print axioms Local4928.equivalent
