import ThreeSlots5060
open PEqualNP.AndCount PEqualNP.Outside.L_meta_7533
namespace Local5060
def narrowAt (A : Finset V) := Finset.univ.filter fun x : V => (A \ neighbors x).card ≤ 1

theorem uniqueCenter (A : Finset V) (large : 4 ≤ A.card) : (narrowAt A).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra ne
  have h₁ := (Finset.mem_filter.mp hx).2
  have h₂ := (Finset.mem_filter.mp hy).2
  have h₃ := Finset.card_union_le (A \ neighbors x) (A \ neighbors y)
  rw [← Finset.sdiff_inter_distrib_right] at h₃
  have h₄ := Finset.card_sdiff_add_card_inter A (neighbors x ∩ neighbors y)
  have h₅ := (Finset.card_le_card (Finset.inter_subset_right (s₁ := A) (s₂ := neighbors x ∩ neighbors y))).trans (intersections x y ne)
  omega

theorem twoLargeSides {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    {v : V} {s t u : Slot C} (covered : positions C v ⊆ {s,t,u})
    (ht : 5 ≤ (raw C t).card) (hu : 5 ≤ (raw C u).card) : (raw C s).card ≤ 3 := by
  let A := (raw C t).erase v
  let B := (raw C u).erase v
  have sub : (raw C s).erase v ⊆ narrowAt A ∪ narrowAt B := by
    intro m hm
    rcases thinAlternate hc out covered hm with h|h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have er (R : Finset V) : R.card ≤ (R.erase v).card + 1 := by
    by_cases h : v ∈ R
    · exact (Finset.card_erase_add_one h).symm.le
    · simp [Finset.erase_eq_of_notMem h]
  have h₁ := uniqueCenter A (by dsimp [A]; have := er (raw C t); omega)
  have h₂ := uniqueCenter B (by dsimp [B]; have := er (raw C u); omega)
  have h₃ := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
  have h₄ := er (raw C s)
  omega
end Local5060
#print axioms Local5060.twoLargeSides
