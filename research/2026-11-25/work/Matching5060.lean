import PEqualNP.Outside.L_meta_7533
open PEqualNP.AndCount PEqualNP.Outside.L_meta_7533

namespace Local5060
set_option maxHeartbeats 1500000
theorem mixedMatching {C : AndCountCircuit 42} (hc : C.Computes plane)
    (out : C.outVars = ∅) (sz : C.size = 19)
    (cap : ∀ v, (positions C v).card ≤ 4) :
    ∃ M : Finset (Slot C), 4 ≤ M.card ∧
      (∀ s ∈ M, ∃ p l, color p = true ∧ color l = false ∧ raw C s = {p,l}) ∧
      ∀ s ∈ M, ∀ t ∈ M, s ≠ t → Disjoint (raw C s) (raw C t) := by
  classical
  choose f hf onlyV using fun v => private_slot hc out v (cap v)
  let vertices (b : Bool) := Finset.univ.filter fun v : V => color v = b
  let slots (b : Bool) := (vertices b).image f
  have small (b : Bool) : (vertices b).card = 21 := by cases b <;> decide +kernel
  have slotCard (b : Bool) : (slots b).card = 21 := by
    change ((vertices b).image f).card = 21
    rw [← small b]
    apply Finset.card_image_of_injOn
    intro v hv w hw e
    apply onlyV w v
    · rw [← e]
      exact mem_positions.mp (hf v)
    · exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
  let M := slots true ∩ slots false
  have unionBound := Finset.card_le_univ (slots true ∪ slots false)
  simp [Slot,sz] at unionBound
  have sumCard := Finset.card_union_add_card_inter (slots true) (slots false)
  rw [slotCard,slotCard] at sumCard
  have reps (s) (hs : s ∈ M) (b : Bool) :
      ∃ v, color v = b ∧ f v = s := by
    have inSlots : s ∈ slots b := by
      cases b
      · exact (Finset.mem_inter.mp hs).2
      · exact (Finset.mem_inter.mp hs).1
    obtain ⟨v,hv,e⟩ := Finset.mem_image.mp inSlots
    exact ⟨v,(Finset.mem_filter.mp hv).2,e⟩
  have forces (s) (hs : s ∈ M) (x) (hx : x ∈ raw C s) : f x = s := by
    obtain ⟨v,hv,e⟩ := reps s hs (color x)
    have eq := onlyV v x (e ▸ hx) hv.symm
    rwa [eq]
  refine ⟨M, by dsimp [M]; omega, ?_, ?_⟩
  · intro s hs
    obtain ⟨p,hp,ep⟩ := reps s hs true
    obtain ⟨l,hl,el⟩ := reps s hs false
    refine ⟨p,l,hp,hl,?_⟩
    ext x
    simp only [Finset.mem_insert,Finset.mem_singleton]
    constructor
    · intro hx
      cases h : color x
      · exact Or.inr (onlyV l x (el ▸ hx) (h.trans hl.symm))
      · exact Or.inl (onlyV p x (ep ▸ hx) (h.trans hp.symm))
    · rintro (rfl|rfl)
      · exact ep ▸ mem_positions.mp (hf x)
      · exact el ▸ mem_positions.mp (hf x)
  · intro s hs t ht ne
    exact Finset.disjoint_left.mpr fun {_} hx hy => ne ((forces s hs _ hx).symm.trans (forces t ht _ hy))
end Local5060
#print axioms Local5060.mixedMatching
