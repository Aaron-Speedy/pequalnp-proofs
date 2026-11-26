import PoolCharge4697
namespace PoolCharge4697
variable {V I : Type*} [DecidableEq V] [DecidableEq I]
theorem packed (B : List (Finset V)) (S : Finset I) (R : I → Finset V)
    (overlap : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((R i) ∩ (R j)).card ≤ 1) :
    ∑ i ∈ S, charges B (R i) ≤ B.length := by
  induction B with
  | nil => simp [charges]
  | cons a T ih =>
    let hit := fun i => 2 ≤ a.card ∧ a ⊆ R i
    have step (i : I) : charges (a::T) (R i) = charges T (R i) + (if hit i then 1 else 0) := by
      by_cases h : hit i
      · simp [charges,hit] at h ⊢; simp [h]
      · unfold hit at h; simp [charges,h,hit]
    have uniq : (S.filter hit).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      obtain ⟨si,_,ai⟩ := Finset.mem_filter.mp hi
      obtain ⟨sj,big,aj⟩ := Finset.mem_filter.mp hj
      by_contra ne
      have ub := overlap i si j sj ne
      have lb := Finset.card_le_card (Finset.subset_inter ai aj)
      omega
    simp_rw [step]
    rw [Finset.sum_add_distrib]
    have e : (∑ i ∈ S, if hit i then 1 else 0) = (S.filter hit).card := by
      simp
    rw [e,List.length_cons]
    omega

theorem totalCost (B : List (Finset V)) (S : Finset I) (R : I → Finset V)
    (pool : Pool B) (small : ∀ i ∈ S, (R i).card ≤ 3)
    (ready : ∀ i ∈ S, (R i).card ≤ 1 ∨ R i ∈ B)
    (overlap : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((R i) ∩ (R j)).card ≤ 1) :
    ∑ i ∈ S, (R i).card ≤ B.length + S.card := by
  have one := Finset.sum_le_sum (fun i hi => covered B (R i) (small i hi) pool (ready i hi))
  have cap := packed B S R overlap
  simpa [Finset.sum_add_distrib] using one.trans (by simpa [Finset.sum_add_distrib] using Nat.add_le_add_right cap S.card)
end PoolCharge4697
#print axioms PoolCharge4697.totalCost
