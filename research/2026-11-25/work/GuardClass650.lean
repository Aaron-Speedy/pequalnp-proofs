import Guard650

namespace Guard650

def neighbors (s : Row) : Row := Finset.univ.filter fun v =>
  ∃ u ∈ s, edge u v ∨ edge v u

theorem insertHit (s : Row) (v : V) (off : ¬ hit s) :
    hit (insert v s) ↔ v ∈ neighbors s := by
  simp only [neighbors,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,ha,b,hb,e⟩
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · obtain ⟨h,k,_⟩ := e; omega
    · exact ⟨b,hb,Or.inr e⟩
    · exact ⟨a,ha,Or.inl e⟩
    · exact (off ⟨a,ha,b,hb,e⟩).elim
  · rintro ⟨u,hu,h | h⟩
    · exact ⟨u,Finset.mem_insert_of_mem hu,v,Finset.mem_insert_self ..,h⟩
    · exact ⟨v,Finset.mem_insert_self ..,u,Finset.mem_insert_of_mem hu,h⟩

theorem determinedMask (H : Row → Prop) (mono : Monotone H) (G : Row)
    (exactOn : ∀ t, hit t ↔ H t ∧ ∃ v ∈ G, v ∈ t)
    {s : Row} (hs : H s) (off : ¬ hit s) : G = neighbors s := by
  have dis (v) (vg : v ∈ G) : v ∉ s := fun vs => off ((exactOn _).mpr ⟨hs,v,vg,vs⟩)
  ext v
  rw [← insertHit s v off]
  constructor
  · intro vg
    exact (exactOn _).mpr ⟨mono (Finset.subset_insert ..) hs,v,vg,Finset.mem_insert_self ..⟩
  · intro h
    obtain ⟨w,wg,hw⟩ := ((exactOn _).mp h).2
    rcases Finset.mem_insert.mp hw with rfl | ws
    · exact wg
    · exact (dis _ wg ws).elim

theorem guardCriterion (H : Row → Prop) (mono : Monotone H) (G : Row) :
    (∀ t, hit t ↔ H t ∧ ∃ v ∈ G, v ∈ t) ↔
    (∀ t, hit t → H t) ∧
    (∀ a b, edge a b → a ∈ G ∨ b ∈ G) ∧
    (∀ s, H s → ¬ hit s → G = neighbors s) := by
  constructor
  · intro h
    refine ⟨fun s e => ((h s).mp e).1,?_,fun _ => determinedMask H mono G h⟩
    intro a b ab
    have e : hit {a,b} := ⟨a,by simp,b,by simp,ab⟩
    obtain ⟨w,wg,hw⟩ := ((h _).mp e).2
    rcases (show w = a ∨ w = b by simpa using hw) with rfl | rfl
    · exact Or.inl wg
    · exact Or.inr wg
  · rintro ⟨major,cover,determined⟩ s
    constructor
    · intro e
      refine ⟨major s e,?_⟩
      obtain ⟨a,ha,b,hb,ab⟩ := e
      rcases cover a b ab with g | g
      · exact ⟨a,g,ha⟩
      · exact ⟨b,g,hb⟩
    · rintro ⟨hs,v,vg,vs⟩
      by_contra off
      rw [determined s hs off,← insertHit s v off,Finset.insert_eq_of_mem vs] at vg
      exact off vg

theorem oneException (H : Row → Prop) (mono : Monotone H) (U : Row) (indep : ¬ hit U) :
    (∀ s, hit s ↔ H s ∧ ∃ v ∈ s, v ∉ U) ↔
    (∀ a b, edge a b → H {a,b}) ∧
    (∀ t, Maximal (fun s => ¬ hit s) t → H t → t = U) := by
  classical
  constructor
  · intro h
    refine ⟨fun a b ab => ((h _).mp ⟨a,by simp,b,by simp,ab⟩).1,?_⟩
    intro t maximal ht
    have sub : t ⊆ U := by
      intro v hv
      by_contra out
      exact maximal.1 ((h t).mpr ⟨ht,v,hv,out⟩)
    exact Finset.Subset.antisymm sub (maximal.2 indep sub)
  · rintro ⟨positive,negative⟩ s
    constructor
    · rintro ⟨a,ha,b,hb,e⟩
      have pair : ({a,b} : Row) ⊆ s := by
        intro v hv
        rcases (show v = a ∨ v = b by simpa using hv) with rfl | rfl
        · exact ha
        · exact hb
      refine ⟨mono pair (positive a b e),?_⟩
      by_cases u : a ∈ U
      · exact ⟨b,hb,fun v => indep ⟨a,u,b,v,e⟩⟩
      · exact ⟨a,ha,u⟩
    · rintro ⟨hs,v,hv,out⟩
      by_contra off
      obtain ⟨t,st,maximal⟩ := Finite.exists_le_maximal (p := fun s => ¬ hit s) off
      exact out (negative t maximal (mono st hs) ▸ st hv)

end Guard650
#print axioms Guard650.guardCriterion
#print axioms Guard650.oneException
