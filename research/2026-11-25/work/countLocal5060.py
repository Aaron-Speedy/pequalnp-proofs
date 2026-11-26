from pathlib import Path
src=Path('lean/PEqualNP/Outside/L_meta_7537.lean').read_text()
layout=src[src.index('lemma obtain_layout'):src.index('section TwoReads')].replace('lemma obtain_layout','lemma obtainLayoutFour').replace('≤ 2)', '≤ 4)').replace('((cap v).trans (by decide))','(cap v)')
out='import LocalPack5060\nopen PEqualNP.AndCount PEqualNP.Outside.L_meta_7537\nnamespace LocalPack5060\n'+layout+'''
theorem fewLow {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (cap : ∀ v, (positions C v).card ≤ 4) :
    (Finset.univ.filter fun v : V => lowAt C v).card ≤ 2*C.size := by
  classical
  obtain ⟨p,q,layout⟩ := obtainLayoutFour hc out cap
  let D := Finset.univ.filter fun v : V => lowAt C v
  let A := D.image q
  let fiber (s : Slot C) := D.filter fun v => q v = s
  let S := D.filter fun v => 1 < (fiber (q v)).card
  have good {v : V} (h : v ∈ D) : lowAt C v := (Finset.mem_filter.mp h).2
  have isPaired {v : V} (h : v ∈ S) : paired q v := by
    obtain ⟨hv,hn⟩ := Finset.mem_filter.mp h
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp hn
    obtain ⟨am,ea⟩ := Finset.mem_filter.mp ha
    obtain ⟨bm,eb⟩ := Finset.mem_filter.mp hb
    by_cases av : a = v
    · exact ⟨b,av ▸ ne.symm,eb,good hv,good bm⟩
    · exact ⟨a,av,ea,good hv,good am⟩
  have isShared {v : V} (h : v ∈ S) : Shared q v := by
    obtain ⟨w,ne,eq,_,_⟩ := isPaired h
    exact ⟨_,ne,eq⟩
'''
s=src[src.index('  let reserved (s : Slot C)'):src.index('  have countAt (s : Slot C)')]
s='\n'.join(l for l in s.split('\n') if 'have isShared ' not in l)
s=s.replace('isShared.mp','isShared').replace('triple_spare hc out hd layout cap','loc_triple_spare hc out hd layout').replace('(isShared (fm ha).1) (isShared (fm hb).1) (isShared (fm hc\').1)','(isPaired (fm ha).1) (isPaired (fm hb).1) (isPaired (fm hc\').1)')
out+=s+'''
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
#print axioms LocalPack5060.fewLow
'''
Path('.pnp/CountLocal5060.lean').write_text(out)
