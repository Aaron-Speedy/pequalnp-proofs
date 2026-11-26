import ReadSupport4928
import Interface4928
open PEqualNP.CircuitLowerBounds LocalFano4126
namespace Local4928
def external (pre post : List Gate) (out : ℕ) :=
  (references post out).filter fun i => decide (i < 14+pre.length)

theorem laterUsed (pre post : List Gate) (out : ℕ) (val : Valid ⟨pre ++ post,out⟩) :
    ∀ i ∈ Finset.Ico (14+pre.length) (14+pre.length+post.length), i ∈ references post out := by
  induction post generalizing pre with
  | nil => simp
  | cons g gs ih =>
    intro i hi
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hi
    have expand {j} (h : j ∈ references gs out) : j ∈ references (g::gs) out := by
      simpa [references] using (show j=out ∨ j∈g.inputs ∨ j∈gs.flatMap Gate.inputs from (List.mem_cons.mp h).imp_right Or.inr)
    by_cases e : i = 14+pre.length
    · subst i; exact expand (allRead pre gs g out val)
    · apply expand
      apply ih (pre ++ [g]) (by simpa using val)
      apply Finset.mem_Ico.mpr
      simp only [List.length_cons,List.length_append,List.length_nil] at *
      omega

theorem externalBound (pre post : List Gate) (out : ℕ) (val : Valid ⟨pre ++ post,out⟩) :
    (external pre post out).length ≤ post.length + 1 := by
  let m := 14+pre.length
  let R := references post out
  let inn := R.filter fun i => !(decide (i < m))
  have live : Finset.Ico m (m+post.length) ⊆ inn.toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨laterUsed pre post out val i hi,by
      simp only [Bool.not_eq_true',decide_eq_false_iff_not,not_lt]; exact (Finset.mem_Ico.mp hi).1⟩)
  have il := (Finset.card_le_card live).trans inn.toFinset_card_le
  rw [Nat.card_Ico] at il
  have partition := R.length_eq_countP_add_countP (fun i => decide (i < m))
  simp only [List.countP_eq_length_filter] at partition
  have binary : ∀ g ∈ post, g.inputs.length = 2 := by
    intro g hg
    obtain ⟨_,a,b,h⟩ := shapeOf val.2.1 g (List.mem_append_right _ hg)
    simp [h]
  have lenFlat (gs : List Gate) (bin : ∀ g ∈ gs, g.inputs.length = 2) : (gs.flatMap Gate.inputs).length = 2*gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,bin g List.mem_cons_self,
        ih (fun k hk => bin k (List.mem_cons_of_mem _ hk))]
      omega
  have lenR : R.length = 2*post.length+1 := by simp [R,references,lenFlat post binary]
  change R.length = (external pre post out).length + inn.length at partition
  omega

end Local4928
#print axioms Local4928.externalBound
