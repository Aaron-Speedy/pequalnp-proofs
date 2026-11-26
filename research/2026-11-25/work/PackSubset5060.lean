import CountLocal5060
open PEqualNP.AndCount PEqualNP.Outside.L_meta_7537
namespace LocalPack5060
theorem packSubset {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    {p q : V → Slot C} (layout : Layout C p q) (D : Finset V)
    (collision : ∀ v ∈ D, ∀ w ∈ D, v ≠ w → q v = q w → lowAt C v ∧ lowAt C w) :
    D.card ≤ 2*C.size := by
  classical
  let A := D.image q
  let fiber (s : Slot C) := D.filter fun v => q v = s
  let S := D.filter fun v => 1 < (fiber (q v)).card
  have isPaired {v : V} (h : v ∈ S) : paired q v := by
    obtain ⟨hv,hn⟩ := Finset.mem_filter.mp h
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp hn
    obtain ⟨am,ea⟩ := Finset.mem_filter.mp ha
    obtain ⟨bm,eb⟩ := Finset.mem_filter.mp hb
    by_cases av : a = v
    · exact ⟨b,av ▸ ne.symm,eb,(collision v hv b bm (av ▸ ne) eb.symm).1,(collision v hv b bm (av ▸ ne) eb.symm).2⟩
    · exact ⟨a,av,ea,(collision v hv a am (Ne.symm av) ea.symm).1,(collision v hv a am (Ne.symm av) ea.symm).2⟩
  have isShared {v : V} (h : v ∈ S) : Shared q v := by
    obtain ⟨w,ne,eq,_,_⟩ := isPaired h
    exact ⟨_,ne,eq⟩
  let reserved (s : Slot C) := Pure C s ∨ s ∈ A
  let f (v : V) := if reserved (other (q v)) then p v else other (q v)
  let B := S.image f
  have notPrivate (v : V) (hv : Shared q v) : ∀ z, ¬ Private C z (p v) := by
    obtain ⟨w,ne,eq⟩ := hv
    intro z h
    obtain ⟨b,e⟩ := (layout v).2.1
    have vz : v = z := h.2 v (layout v).1 ((e v (layout v).1).trans (e z h.1).symm)
    subst z
    exact (shared_data layout ne eq).2.2 ⟨p v, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨h.1, fun x hx => h.2 x hx ((e x hx).trans (e v h.1).symm)⟩⟩
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro s ha hb
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp ha
    by_cases r : reserved (other (q v))
    · have e : q z = p v := by simpa only [f, ite_eq_left r] using eq
      exact notPrivate v (isShared hv) z (e ▸ (layout z).2.2.1)
    · have e : q z = other (q v) := by simpa only [f, ite_eq_right r] using eq
      exact r (Or.inr (Finset.mem_image.mpr ⟨z, hz, e⟩))
  have qFiber (s : Slot C) :
      ((Finset.univ : Finset V).filter fun v => q v = s).card ≤ 2 := by
    have h := Finset.card_le_card_of_injOn color
      (t := (Finset.univ : Finset Bool)) (s := (Finset.univ : Finset V).filter fun v => q v = s)
      (fun _ _ => Finset.mem_univ _) (by
        intro v hv w hw col
        exact private_inj layout col ((Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2.trans
          (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2.symm))
    simpa using h
  have fFiber (s : Slot C) : (S.filter fun v => f v = s).card ≤ 2 := by
    have fm {v : V} (hv : v ∈ S.filter fun v => f v = s) := Finset.mem_filter.mp hv
    by_cases hPure : Pure C s
    · have fromPure {v : V} (hv : v ∈ S.filter fun v => f v = s) :
          reserved (other (q v)) ∧ p v = s := by
        have eq := (fm hv).2
        by_cases r : reserved (other (q v))
        · exact ⟨r, by simpa only [f, ite_eq_left r] using eq⟩
        · have e : other (q v) = s := by simpa only [f, ite_eq_right r] using eq
          exact (r (Or.inl (e.symm ▸ hPure))).elim
      by_contra! h
      obtain ⟨a,ha,b,hb,c,hc',ab,ac,bc⟩ := Finset.two_lt_card.mp h
      have ha' := fromPure ha
      have hSpare := loc_triple_spare hc out hd layout ab ac bc
        ((fromPure hb).2.trans ha'.2.symm) ((fromPure hc').2.trans ha'.2.symm)
        (isPaired (fm ha).1) (isPaired (fm hb).1) (isPaired (fm hc').1)
      rcases ha'.1 with h | h
      · exact hSpare.1 h
      · obtain ⟨z,_,eq⟩ := Finset.mem_image.mp h
        exact hSpare.2 z (eq ▸ (layout z).2.2.1)
    · have fromMixed {v : V} (hv : v ∈ S.filter fun v => f v = s) : q v = other s := by
        have eq := (fm hv).2
        by_cases r : reserved (other (q v))
        · have e : p v = s := by simpa only [f, ite_eq_left r] using eq
          exact (hPure (e ▸ (layout v).2.1)).elim
        · have e : other (q v) = s := by simpa only [f, ite_eq_right r] using eq
          rw [← e, other_other]
      refine (Finset.card_le_card ?_).trans (qFiber (other s))
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fromMixed hv⟩
  have sharedCount : S.card ≤ 2 * B.card := by
    rw [Finset.card_eq_sum_card_fiberwise (fun v hv => Finset.mem_image_of_mem f hv)]
    calc
      (∑ s ∈ B, (S.filter fun v => f v = s).card) ≤ ∑ _s ∈ B, 2 :=
        Finset.sum_le_sum fun s _ => fFiber s
      _ = 2 * B.card := by simp [Nat.mul_comm]

  have countAt (s : Slot C) (hs : s ∈ A) :
      2 * (fiber s).card = 2 + (S.filter fun v => q v = s).card := by
    obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hs
    have vm : v ∈ fiber s := Finset.mem_filter.mpr ⟨hv,eq⟩
    have lo := Finset.card_pos.mpr ⟨v,vm⟩
    have hi : (fiber s).card ≤ 2 := (Finset.card_le_card (show fiber s ⊆
      (Finset.univ.filter fun v : V => q v = s) from fun x hx =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩)).trans (qFiber s)
    by_cases h : 1 < (fiber s).card
    · have same : (S.filter fun v => q v = s) = fiber s := by
        ext x
        simp only [S,fiber,Finset.mem_filter]
        constructor
        · exact fun ⟨⟨hx,_⟩,e⟩ => ⟨hx,e⟩
        · rintro ⟨hx,e⟩
          exact ⟨⟨hx, e ▸ h⟩,e⟩
      rw [same]; omega
    · have emp : (S.filter fun v => q v = s) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨hS,e⟩ := Finset.mem_filter.mp hx
        exact h (e ▸ (Finset.mem_filter.mp hS).2)
      rw [emp,Finset.card_empty]; omega
  have accounted : 2 * D.card = 2 * A.card + S.card := by
    have all := Finset.card_eq_sum_card_fiberwise (s := D) (t := A) (f := q)
      (fun v hv => Finset.mem_image_of_mem q hv)
    have sh := Finset.card_eq_sum_card_fiberwise (s := S) (t := A) (f := q)
      (fun v hv => Finset.mem_image_of_mem q (Finset.mem_filter.mp hv).1)
    calc
      2*D.card = 2 * ∑ s ∈ A, (fiber s).card := congrArg (fun n : ℕ => 2*n) all
      _ = ∑ s ∈ A, 2 * (fiber s).card := Finset.mul_sum .. 
      _ = ∑ s ∈ A, (2 + (S.filter fun v => q v = s).card) := Finset.sum_congr rfl countAt
      _ = 2 * A.card + S.card := by rw [Finset.sum_add_distrib,← sh]; simp [Nat.mul_comm]
  have total := Finset.card_le_univ (A ∪ B)
  rw [Finset.card_union_of_disjoint dis] at total
  simp [Fintype.card_prod] at total
  change D.card ≤ _
  omega
end LocalPack5060
#print axioms LocalPack5060.packSubset
