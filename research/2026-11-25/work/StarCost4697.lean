import PackedCharge4697
namespace PoolCharge4697
variable {V I : Type*} [DecidableEq V] [DecidableEq I]
/-- One center can occur several times. Only a center used once may need to
charge the union pool to pay for its incident edges. -/
theorem starCost (B : List (Finset V)) (S : Finset I) (R : I → Finset V)
    (uses : I → ℕ) (nonzero : ∀ i ∈ S, 0 < uses i)
    (pool : Pool B) (small : ∀ i ∈ S, (R i).card ≤ 3)
    (ready : ∀ i ∈ S, uses i = 1 → (R i).card ≤ 1 ∨ R i ∈ B)
    (overlap : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((R i) ∩ (R j)).card ≤ 1) :
    (∑ i ∈ S, (R i).card) + S.card ≤ B.length + 2 * ∑ i ∈ S, uses i := by
  have point (i : I) (hi : i ∈ S) :
      (R i).card + 1 ≤ charges B (R i) + 2 * uses i := by
    have sm := small i hi
    have positive := nonzero i hi
    by_cases once : uses i = 1
    · have h := covered B (R i) sm pool (ready i hi once)
      omega
    · omega
  have h := Finset.sum_le_sum point
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one,← Finset.mul_sum] at h
  have bound := packed B S R overlap
  omega
end PoolCharge4697
#print axioms PoolCharge4697.starCost
