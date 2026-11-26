import PrefixBound4928
open Features4928 LocalFano4126 PEqualNP.CircuitLowerBounds
namespace Local4928
theorem tightReferences (pre post : List Gate) (out : ℕ) (val : Valid ⟨pre ++ post,out⟩)
    (labels : ℕ → Token) (obs : Observed pre post out labels) (len : post.length = 13) :
    (references post out).Nodup := by
  let R := references post out
  let E := external pre post out
  let I := Finset.Ico (14+pre.length) (14+pre.length+post.length)
  obtain ⟨en,small⟩ := interfaceClassification _ (suffixEnough pre post out val labels obs)
  have eb := externalBound pre post out val
  rw [List.length_map] at en
  have eq : E.length = 14 := by change (external pre post out).length = 14; omega
  have nd : E.Nodup := by
    apply List.Nodup.of_map labels
    exact (small (by rw [List.length_map]; exact eq.le)).1
  have sub : E.toFinset ∪ I ⊆ R.toFinset := by
    intro i hi
    rcases Finset.mem_union.mp hi with ext|inside
    · exact List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp ext)).1
    · exact List.mem_toFinset.mpr (laterUsed pre post out val i inside)
  have dis : Disjoint E.toFinset I := by
    apply Finset.disjoint_left.mpr
    intro i he hi
    exact (not_lt_of_ge (Finset.mem_Ico.mp hi).1)
      (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp he)).2)
  have low := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup nd,eq] at low
  have ci : I.card = 13 := by simp [I,len]
  rw [ci] at low
  have refLen : R.length = 27 := by
    have b : ∀ t ∈ post, t.inputs.length = 2 := by
      intro t ht
      obtain ⟨_,a,c,ins⟩ := shapeOf val.2.1 t (List.mem_append_right _ ht)
      simp [ins]
    have f (gs : List Gate) (h : ∀ t ∈ gs, t.inputs.length = 2) : (gs.flatMap Gate.inputs).length = 2*gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        simp only [List.flatMap_cons,List.length_append,List.length_cons,h _ List.mem_cons_self,
          ih (fun t ht => h _ (List.mem_cons_of_mem _ ht))]
        omega
    simp [R,references,f post b,len]
  apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (R : Multiset ℕ))).mp
  change R.toFinset.card = R.length
  have upper := R.toFinset_card_le
  omega
end Local4928
#print axioms Local4928.tightReferences
