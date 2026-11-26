import PEqualNP.Outside.L_meta_7537
open PEqualNP.AndCount PEqualNP.Outside.L_meta_7537
namespace LocalPack5060
variable {C : AndCountCircuit 42} {p q : V → Slot C}
abbrev lowAt (C : AndCountCircuit 42) (v : V) := (positions C v).card ≤ 2
def paired (q : V → Slot C) (v : V) := ∃ w, w ≠ v ∧ q w = q v ∧ lowAt C v ∧ lowAt C w
lemma loc_positions_two (layout : Layout C p q)
    {v : V} (lov : lowAt C v) (ns : ¬ Solo C v) : positions C v = {p v, q v} := by
  have ne : p v ≠ q v := by
    intro e
    apply ns
    refine ⟨p v, Finset.eq_singleton_iff_unique_mem.mpr ⟨(layout v).1, ?_⟩⟩
    intro w hw
    exact (layout v).2.2.1.2 w (e ▸ hw) (pure_color layout hw)
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact mem_positions.mpr (layout v).1
    · exact mem_positions.mpr (layout v).2.2.1.1
  · simpa [ne] using lov

lemma loc_shared_adj (hc : C.Computes plane) (out : C.outVars = ∅)
    (layout : Layout C p q)
    {v w z : V} (lov : lowAt C v) (wv : w ≠ v) (eq : q w = q v)
    (hz : z ∈ raw C (p v)) (zv : z ≠ v) : plane.Adj w z := by
  have data := shared_data layout wv eq
  exact (two_companions hc out (loc_positions_two layout lov data.2.2) zv wv hz
    (eq ▸ (layout w).2.2.1.1)).symm

lemma loc_covered_two (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q)
    {v w : V} (lov : lowAt C v) (sh : Shared q v) (edge : plane.Adj v w) :
    w ∈ raw C (other (p v)) ∨ w ∈ raw C (other (q v)) := by
  obtain ⟨u, uv, eq⟩ := sh
  obtain ⟨s, hs, h⟩ := witness hc out hd edge
  rw [loc_positions_two layout lov (shared_data layout uv eq).2.2] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

lemma loc_mate_pure_card (hc : C.Computes plane) (out : C.outVars = ∅)
    (layout : Layout C p q)
    {v w : V} (lov : lowAt C v) (wv : w ≠ v) (eq : q w = q v) : (raw C (p v)).card ≤ 6 := by
  have sub : raw C (p v) ⊆ insert v (neighbors w) := by
    intro z hz
    by_cases e : z = v
    · exact Finset.mem_insert.mpr (Or.inl e)
    · exact Finset.mem_insert_of_mem (mem_neighbors.mpr (loc_shared_adj hc out layout lov wv eq hz e))
  have h := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
  rw [degree] at h
  exact h

lemma loc_pure_three_card (hc : C.Computes plane) (out : C.outVars = ∅)
    (layout : Layout C p q)
    {a b c u v : V} (loa : lowAt C a) (lob : lowAt C b) (ab : a ≠ b) (ca : c ≠ a) (cb : c ≠ b)
    (pb : p b = p a) (pc : p c = p a)
    (ua : u ≠ a) (vb : v ≠ b) (qu : q u = q a) (qv : q v = q b) :
    (raw C (p a)).card ≤ 3 := by
  have col := pure_color layout (pb ▸ (layout b).1)
  have qne : q a ≠ q b := fun e => ab (private_inj layout col.symm e)
  have ne : u ≠ v := fun e => qne (qu.symm.trans ((congrArg q e).trans qv))
  have cm : c ∈ raw C (p a) := pc ▸ (layout c).1
  have uc := loc_shared_adj hc out layout loa ua qu cm ca
  have vc := loc_shared_adj hc out layout lob vb qv (pb.symm ▸ cm) cb
  have sub : raw C (p a) ⊆ ({a,b,c} : Finset V) := by
    intro z hz
    by_cases za : z = a
    · simp [za]
    by_cases zb : z = b
    · simp [zb]
    have uz := loc_shared_adj hc out layout loa ua qu hz za
    have vz := loc_shared_adj hc out layout lob vb qv (pb.symm ▸ hz) zb
    simp [unique_common ne uz vz uc vc]
  exact (Finset.card_le_card sub).trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right Finset.card_le_two 1))

lemma loc_mate_on_opposite (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q)
    {v w : V} (low : lowAt C w) (wv : w ≠ v) (eq : q w = q v)
    (hw : w ∈ raw C (other (p v))) : p w = other (p v) := by
  have h := mem_positions.mpr hw
  rw [loc_positions_two layout low (shared_data layout wv.symm eq.symm).2.2] at h
  rcases Finset.mem_insert.mp h with e | e
  · exact e.symm
  · have bad := (Finset.mem_singleton.mp e).trans eq
    exact ((Finset.disjoint_left.mp (raw_disjoint_other hd (p v))) (layout v).1
      (bad.symm ▸ (layout v).2.2.1.1)).elim

lemma loc_triple_mixed_separate (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q)
    {a b c : V} (ab : a ≠ b) (ca : c ≠ a) (cb : c ≠ b)
    (pb : p b = p a) (pc : p c = p a)
    (sa : paired q a) (sb : paired q b) (sc : paired q c) :
    other (q a) ≠ q b := by
  obtain ⟨u, ua, qu, loa, lou⟩ := sa
  obtain ⟨v, vb, qv, lob, lov⟩ := sb
  obtain ⟨w, wc, qw, loc, low⟩ := sc
  have col := pure_color layout (pb ▸ (layout b).1)
  have wcol := pure_color layout (pc ▸ (layout c).1)
  have dara := shared_data layout ua qu
  have darb := shared_data layout vb qv
  have darc := shared_data layout wc qw
  intro op
  have op' : other (q b) = q a := by rw [← op, other_other]
  have wa := loc_shared_adj hc out layout loc wc qw (pc.symm ▸ (layout a).1) ca.symm
  have wr : w ∈ raw C (other (p a)) := by
    rcases loc_covered_two hc out hd layout loa ⟨u,ua,qu⟩ wa.symm with h | h
    · exact h
    · rw [op, darb.2.1, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with e | e
      · exact (darc.1 (by rw [e, col, wcol])).elim
      · have same : q c = q b := qw.symm.trans ((congrArg q e).trans qv)
        have eq : c = b := private_inj layout (wcol.trans col.symm) same
        exact (cb eq).elim
  have pureW := loc_mate_on_opposite hd layout low wc qw (pc ▸ wr)
  have small := loc_mate_pure_card hc out layout low wc.symm qw.symm
  rw [pureW, pc] at small
  have cover (x y t : V) (sx : paired q x) (px : p x = p a)
      (opp : raw C (other (q x)) = {y,t}) (same : color y = color x) :
      neighbors x ⊆ insert t (raw C (other (p a))) := by
    intro z hz
    have e := mem_neighbors.mp hz
    rcases loc_covered_two hc out hd layout (by obtain ⟨_,_,_,h,_⟩ := sx; exact h) (by obtain ⟨w,ne,eq,_,_⟩ := sx; exact ⟨w,ne,eq⟩) e with h | h
    · exact Finset.mem_insert_of_mem (px ▸ h)
    · rw [opp, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact ((cross e) same.symm).elim
      · exact Finset.mem_insert_self _ _
  have large := many_common_targets ab (raw C (other (p a)))
    (cover a b v ⟨u,ua,qu,loa,lou⟩ rfl (by rw [op, darb.2.1]) col)
    (cover b a u ⟨v,vb,qv,lob,lov⟩ pb (by rw [op', dara.2.1]) col.symm)
  omega

lemma loc_triple_mates_opposite (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q)
    {a b c u : V} (loa : lowAt C a) (lou : lowAt C u) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (pb : p b = p a) (pc : p c = p a) (ua : u ≠ a) (qu : q u = q a)
    (sb : paired q b) (sc : paired q c) :
    p u = other (p a) := by
  have sa : paired q a := ⟨u,ua,qu,loa,lou⟩
  have qb : other (q b) ≠ q a :=
    loc_triple_mixed_separate hc out hd layout ab.symm bc.symm ac.symm pb.symm
      (pc.trans pb.symm) sb sa sc
  have qc : other (q c) ≠ q a :=
    loc_triple_mixed_separate hc out hd layout ac.symm bc ab.symm pc.symm
      (pb.trans pc.symm) sc sa sb
  have bcol := pure_color layout (pb ▸ (layout b).1)
  have ccol := pure_color layout (pc ▸ (layout c).1)
  have qbc : q b ≠ q c := fun e => bc (private_inj layout (bcol.trans ccol.symm) e)
  have ub := loc_shared_adj hc out layout loa ua qu (pb ▸ (layout b).1) ab.symm
  have uc := loc_shared_adj hc out layout loa ua qu (pc ▸ (layout c).1) ac.symm
  apply loc_mate_on_opposite hd layout lou ua qu
  by_contra h
  have hitB : u ∈ raw C (other (q b)) :=
    (loc_covered_two hc out hd layout (by obtain ⟨_,_,_,h,_⟩ := sb; exact h) (by obtain ⟨w,ne,eq,_,_⟩ := sb; exact ⟨w,ne,eq⟩) ub.symm).resolve_left (fun e => h (pb ▸ e))
  have hitC : u ∈ raw C (other (q c)) :=
    (loc_covered_two hc out hd layout (by obtain ⟨_,_,_,h,_⟩ := sc; exact h) (by obtain ⟨w,ne,eq,_,_⟩ := sc; exact ⟨w,ne,eq⟩) uc.symm).resolve_left (fun e => h (pc ▸ e))
  have reads := loc_positions_two layout lou (shared_data layout ua.symm qu.symm).2.2
  have one (s : Slot C) (hs : u ∈ raw C s) (ne : s ≠ q a) : s = p u := by
    have hm := mem_positions.mpr hs
    rw [reads, Finset.mem_insert, Finset.mem_singleton, qu] at hm
    exact hm.resolve_right ne
  exact qbc (other_inj ((one _ hitB qb).trans (one _ hitC qc).symm))

lemma loc_triple_spare (hc : C.Computes plane) (out : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (layout : Layout C p q)
    {a b c : V} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (pb : p b = p a) (pc : p c = p a) (sa : paired q a) (sb : paired q b) (sc : paired q c) :
    ¬ Pure C (other (q a)) ∧ ∀ z, ¬ Private C z (other (q a)) := by
  obtain ⟨u, ua, qu, loa, lou⟩ := sa
  obtain ⟨v, vb, qv, lob, lov⟩ := sb
  obtain ⟨w, wc, qw, loc, low⟩ := sc
  have bcol := pure_color layout (pb ▸ (layout b).1)
  have ccol := pure_color layout (pc ▸ (layout c).1)
  have uv : u ≠ v := fun e => ab (private_inj layout bcol.symm
    (qu.symm.trans ((congrArg q e).trans qv)))
  have uw : u ≠ w := fun e => ac (private_inj layout ccol.symm
    (qu.symm.trans ((congrArg q e).trans qw)))
  have vw : v ≠ w := fun e => bc (private_inj layout (bcol.trans ccol.symm)
    (qv.symm.trans ((congrArg q e).trans qw)))
  have pu := loc_triple_mates_opposite hc out hd layout loa lou ab ac bc pb pc ua qu
    ⟨v,vb,qv,lob,lov⟩ ⟨w,wc,qw,loc,low⟩
  have pv := loc_triple_mates_opposite hc out hd layout lob lov ab.symm bc ac pb.symm
    (pc.trans pb.symm) vb qv ⟨u,ua,qu,loa,lou⟩ ⟨w,wc,qw,loc,low⟩
  have pw := loc_triple_mates_opposite hc out hd layout loc low ac.symm bc.symm ab pc.symm
    (pb.trans pc.symm) wc qw ⟨u,ua,qu,loa,lou⟩ ⟨v,vb,qv,lob,lov⟩
  have pvu : p v = p u := by rw [pv,pb,pu]
  have pwu : p w = p u := by rw [pw,pc,pu]
  have smallA := loc_pure_three_card hc out layout loa lob ab ac.symm bc.symm pb pc ua vb qu qv
  have smallU := loc_pure_three_card hc out layout lou lov uv uw.symm vw.symm pvu pwu
    ua.symm vb.symm qu.symm qv.symm
  have sA : (raw C (other (p a))).card ≤ 3 := by rwa [← pu]
  have sU : (raw C (other (p u))).card ≤ 3 := by rwa [pu, other_other]
  have cover (x : V) (sx : paired q x) :
      neighbors x ⊆ raw C (other (p x)) ∪ raw C (other (q x)) := by
    intro z hz
    exact Finset.mem_union.mpr (loc_covered_two hc out hd layout (by obtain ⟨_,_,_,h,_⟩ := sx; exact h) (by obtain ⟨w,ne,eq,_,_⟩ := sx; exact ⟨w,ne,eq⟩) (mem_neighbors.mp hz))
  obtain ⟨x,y,hx,hy,ax,ay,xy⟩ := two_outside sA (cover a ⟨u,ua,qu,loa,lou⟩)
  obtain ⟨i,j,hi,hj,ui,uj,ij⟩ := two_outside sU (cover u ⟨a,ua.symm,qu.symm,lou,loa⟩)
  rw [qu] at hi hj
  have uaCol := (shared_data layout ua qu).1
  have xx : color x = color u :=
    (Bool.eq_not_of_ne (cross ax).symm).trans (Bool.eq_not_of_ne uaCol).symm
  have yy : color y = color u :=
    (Bool.eq_not_of_ne (cross ay).symm).trans (Bool.eq_not_of_ne uaCol).symm
  have ii : color i = color a :=
    (Bool.eq_not_of_ne (cross ui).symm).trans (Bool.eq_not_of_ne (Ne.symm uaCol)).symm
  have jj : color j = color a :=
    (Bool.eq_not_of_ne (cross uj).symm).trans (Bool.eq_not_of_ne (Ne.symm uaCol)).symm
  refine ⟨fun ⟨d,h⟩ => uaCol (xx.symm.trans ((h x hx).trans ((h i hi).symm.trans ii))), ?_⟩
  intro z h
  by_cases e : color z = color a
  · exact ij ((h.2 i hi (ii.trans e.symm)).trans (h.2 j hj (jj.trans e.symm)).symm)
  · have e' : color z = color u := (Bool.eq_not_of_ne e).trans (Bool.eq_not_of_ne uaCol).symm
    exact xy ((h.2 x hx (xx.trans e'.symm)).trans (h.2 y hy (yy.trans e'.symm)).symm)

end LocalPack5060
#print axioms LocalPack5060.loc_triple_spare
