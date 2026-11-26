import PackSubset5060
open PEqualNP.AndCount PEqualNP.Outside.L_meta_7537
namespace LocalPack5060

theorem highPairs {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) {p q : V → Slot C}
    (layout : Layout C p q) :
    42 ≤ 2*C.size + (Finset.univ.filter fun s : Slot C =>
      ∃ v w : V, q v = s ∧ q w = s ∧ v ≠ w ∧ ¬lowAt C v).card := by
  classical
  let bad (s : Slot C) := ∃ v w : V, q v = s ∧ q w = s ∧ v ≠ w ∧ ¬lowAt C v
  let T := Finset.univ.filter bad
  let rep (s : Slot C) : V := if h : bad s then h.choose else 0
  have chosen (s) (h : bad s) : q (rep s) = s := by
    dsimp only [rep]; rw [dif_pos h]; exact h.choose_spec.choose_spec.1
  let lost := T.image rep
  let D := Finset.univ \ lost
  have avoid (s) (h : bad s) : rep s ∉ D := fun hr =>
    (Finset.mem_sdiff.mp hr).2 (Finset.mem_image_of_mem rep (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
  have collision (v) (hv : v ∈ D) (w) (hw : w ∈ D) (ne : v ≠ w) (eq : q v = q w) :
      lowAt C v := by
    by_contra high
    have h : bad (q v) := ⟨v,w,rfl,eq.symm,ne,high⟩
    have e := chosen _ h
    by_cases col : color (rep (q v)) = color v
    · exact avoid _ h ((private_inj layout col e).symm ▸ hv)
    · have diff := (shared_data layout ne eq).1
      have col' : color (rep (q v)) = color w := (Bool.eq_not_of_ne col).trans (Bool.eq_not_of_ne diff.symm).symm
      exact avoid _ h ((private_inj layout col' (e.trans eq)).symm ▸ hw)
  have bound := packSubset hc out hd layout D fun v hv w hw ne eq =>
    ⟨collision v hv w hw ne eq,collision w hw v hv ne.symm eq.symm⟩
  have total : D.card + lost.card = 42 := by
    dsimp only [D]; rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)]
    decide
  have le : lost.card ≤ T.card := Finset.card_image_le
  have result : 42 ≤ 2*C.size + T.card := by omega
  simpa [T,bad] using result

theorem fourHighPairs {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (size : C.size = 19)
    (cap : ∀ v, readCount C v ≤ 3) :
    ∃ M : Finset (Slot C), 4 ≤ M.card ∧
      (∀ s ∈ M, ∃ v w, v ≠ w ∧ color v ≠ color w ∧ raw C s = {v,w} ∧ readCount C v = 3) ∧
      ∀ s ∈ M, ∀ t ∈ M, s ≠ t → Disjoint (raw C s) (raw C t) := by
  classical
  obtain ⟨p,q,layout⟩ := obtainLayoutFour hc out fun v => by rw [positions_card C hd]; exact (cap v).trans (by decide)
  let bad (s : Slot C) := ∃ v w : V, q v = s ∧ q w = s ∧ v ≠ w ∧ ¬lowAt C v
  let M := Finset.univ.filter bad
  have count := highPairs hc out hd layout
  change 42 ≤ 2*C.size + M.card at count
  rw [size] at count
  have data (s) (hs : s ∈ M) : ∃ v w, v ≠ w ∧ color v ≠ color w ∧
      raw C s = {v,w} ∧ readCount C v = 3 ∧ q v = s ∧ q w = s := by
    obtain ⟨v,w,ev,ew,ne,hi⟩ := (Finset.mem_filter.mp hs).2
    have sh := shared_data layout (Ne.symm ne) (ew.trans ev.symm)
    have hr : ¬ readCount C v ≤ 2 := by simpa only [lowAt,positions_card C hd] using hi
    have top := cap v
    exact ⟨v,w,ne,Ne.symm sh.1,ev ▸ sh.2.1,by omega,ev,ew⟩
  have owns (s) (hs : s ∈ M) (x) (hx : x ∈ raw C s) : q x = s := by
    obtain ⟨v,w,_,_,eq,_,ev,ew⟩ := data s hs
    rw [eq,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl <;> assumption
  refine ⟨M,by omega,?_,?_⟩
  · intro s hs
    obtain ⟨v,w,n,c,e,h,_,_⟩ := data s hs
    exact ⟨v,w,n,c,e,h⟩
  · intro s hs t ht ne
    exact Finset.disjoint_left.mpr fun {_} hx hy => ne ((owns s hs _ hx).symm.trans (owns t ht _ hy))
end LocalPack5060
#print axioms LocalPack5060.highPairs
#print axioms LocalPack5060.fourHighPairs
