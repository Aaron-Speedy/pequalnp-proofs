import TightSuffix4928
open PEqualNP.CircuitLowerBounds
namespace Local4928
def budget (r d : List ℕ) := (r.map fun i => d.getD i 0).sum
theorem oneUse (r : List ℕ) (nr : r.Nodup) (i t : ℕ) :
    (r.map fun k => if k=i then t else 0).sum ≤ t := by
  by_cases hi : i ∈ r
  · induction r with
    | nil => simp
    | cons a r ih =>
      by_cases eq : a=i
      · subst a
        have no := (List.nodup_cons.mp nr).1
        have zero : (r.map fun k => if k=i then t else 0) = r.map (fun _ => 0) := by
          apply List.map_congr_left
          intro k hk
          have ne : k ≠ i := fun e => no (e ▸ hk)
          simp [ne]
        simp [zero]
      · have mem := (List.mem_cons.mp hi).resolve_left (Ne.symm eq)
        simpa [eq] using ih nr.of_cons mem
  · have zero : (r.map fun k => if k=i then t else 0) = r.map (fun _ => 0) := by
      apply List.map_congr_left; intro k hk
      have ne : k ≠ i := fun e => hi (e ▸ hk)
      simp [ne]
    simp [zero]
theorem snocBudget (r d : List ℕ) (nr : r.Nodup) (t : ℕ) :
    budget r (d++[t]) ≤ budget r d + t := by
  have eq (i : ℕ) : (d++[t]).getD i 0 = d.getD i 0 + if i=d.length then t else 0 := by
    by_cases lt : i < d.length
    · simp only [List.getD_append _ _ _ _ lt,if_neg (Nat.ne_of_lt lt),Nat.add_zero]
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_eq_default d 0 (by omega)]
      by_cases e : i = d.length
      · simp [e]
      · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [e]
  unfold budget
  simp_rw [eq]
  rw [List.sum_map_add]
  exact Nat.add_le_add_left (oneUse r nr d.length t) _
theorem gateBudget (g : Gate) (d : List ℕ) : g.lineDegree d ≤ budget g.inputs d := by
  unfold Gate.lineDegree budget
  split
  · exact le_rfl
  · generalize g.inputs.map (fun i => d.getD i 0) = l
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.foldr_cons,List.sum_cons,max_le_iff]; omega
theorem readOnceBudget (gs : List Gate) (out : ℕ) (d : List ℕ) (h : (references gs out).Nodup) :
    (gs.foldl (fun w g => w ++ [g.lineDegree w]) d).getD out 0 ≤ budget (references gs out) d := by
  induction gs generalizing d with
  | nil => simp [budget,references]
  | cons g gs ih =>
    have rest : (references gs out).Nodup := by
      exact List.Nodup.sublist (List.Sublist.cons₂ _ (List.sublist_append_right ..)) h
    have use := snocBudget (references gs out) d rest (g.lineDegree d)
    have val := gateBudget g d
    have tail := ih (d ++ [g.lineDegree d]) rest
    simp only [List.foldl_cons]
    have eq : budget (references (g::gs) out) d = budget (references gs out) d + budget g.inputs d := by
      simp [budget,references]; omega
    rw [eq]
    omega
end Local4928
#print axioms Local4928.readOnceBudget
