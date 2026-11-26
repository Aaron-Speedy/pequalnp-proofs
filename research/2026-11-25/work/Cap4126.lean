import SignedRect4126

namespace SignedRect4126
variable {P N : Type} [DecidableEq P] [DecidableEq N]

/-- An exact capacity test for signed rectangle weights. -/
theorem cap_iff (W : P → N → ℤ) (rows : Finset P) (cols : Finset N) (cap : ℤ) :
    (∀ A ⊆ rows, ∀ B ⊆ cols, mass W A B ≤ cap) ↔
    ∀ A ∈ rows.powerset, (∑ j ∈ cols, max 0 (∑ i ∈ A, W i j)) ≤ cap := by
  constructor
  · intro h A hA
    let B := cols.filter fun j => 0 < ∑ i ∈ A, W i j
    have upper := h A (Finset.mem_powerset.mp hA) B (Finset.filter_subset ..)
    unfold mass at upper
    rw [Finset.sum_comm] at upper
    dsimp [B] at upper
    rw [Finset.sum_filter] at upper
    convert upper using 1
    apply Finset.sum_congr rfl
    intro j hj
    split <;> omega
  · intro h A hA B hB
    unfold mass
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ j ∈ B, max 0 (∑ i ∈ A, W i j) :=
        Finset.sum_le_sum fun _ _ => le_max_right .. 
      _ ≤ ∑ j ∈ cols, max 0 (∑ i ∈ A, W i j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hB fun _ _ _ => le_max_left ..
      _ ≤ cap := h A (Finset.mem_powerset.mpr hA)
end SignedRect4126

#print axioms SignedRect4126.cap_iff
