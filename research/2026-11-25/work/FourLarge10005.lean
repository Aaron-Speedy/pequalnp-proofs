import PEqualNP.Outside.L_meta_10004
namespace PEqualNP.Outside.Matrix10005
open PEqualNP.Outside.L_meta_10004_aux
open scoped BigOperators

def area (r : Box) := r.1.card * r.2.card
theorem fourLarge (R : Fin 15 → Box) (good : ∀ t, plain (R t))
    (cover : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    4 ≤ (Finset.univ.filter (fun t => 56 < area (R t))).card := by
  have lower := area_lower R good cover
  let large := Finset.univ.filter (fun t => 56 < area (R t))
  have each (t : Fin 15) : area (R t) ≤ 56 + (if t ∈ large then 4 else 0) := by
    by_cases h : t ∈ large
    · simpa [h,area] using Area.matrix_area_le_60 _ _ (good t)
    · have low : ¬ 56 < area (R t) := by simpa [large] using h
      simp [h]; omega
  have total := Finset.sum_le_sum (s := Finset.univ) (fun t _ => each t)
  have eq : (∑ t : Fin 15, if t ∈ large then 4 else 0) = large.card * 4 := by
    simp [← Finset.sum_filter]
  simp only [Finset.sum_add_distrib,eq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at total
  change 930 ≤ 5 * 15 + ∑ t, area (R t) at lower
  change 4 ≤ large.card
  omega
end PEqualNP.Outside.Matrix10005
#print axioms PEqualNP.Outside.Matrix10005.fourLarge
