import Mathlib

namespace Guard650

abbrev V := Fin 26
abbrev Row := Finset V

abbrev edge (a b : V) : Prop :=
  a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val - 13) % 13 ∈ ([0,1,3,9] : List ℕ)

def hit (s : Row) : Prop := ∃ a ∈ s, ∃ b ∈ s, edge a b

def left (i : Fin 13) : V := Fin.castAdd 13 i
def right (i : Fin 13) : V := Fin.natAdd 13 (-i)

def conflicts (v : V) : Finset (Fin 13) :=
  Finset.univ.filter fun i => decide (edge v (right i) ∨ edge (left i) v)

theorem four (v : V) : (conflicts v).card = 4 := by revert v; decide +kernel
theorem matching (i : Fin 13) : edge (left i) (right i) := by revert i; decide +kernel

theorem unguardedSmall (H : Row → Prop) (mono : Monotone H) (G : Row)
    (exactOn : ∀ s, hit s ↔ H s ∧ ∃ v ∈ G, v ∈ s)
    (s : Row) (small : s.card ≤ 3) : H s ↔ hit s := by
  classical
  refine ⟨fun hs => ?_, fun e => ((exactOn s).mp e).1⟩
  by_contra bad
  have card : (s.biUnion conflicts).card ≤ 12 := calc
    _ ≤ ∑ v ∈ s, (conflicts v).card := Finset.card_biUnion_le
    _ = s.card * 4 := by simp [four]
    _ ≤ 12 := by omega
  obtain ⟨i,hi⟩ : ∃ i : Fin 13, i ∉ s.biUnion conflicts := by
    by_contra! no
    have e : s.biUnion conflicts = Finset.univ := Finset.eq_univ_of_forall no
    simp [e] at card
  have clean (v) (hv : v ∈ s) : ¬ edge v (right i) ∧ ¬ edge (left i) v := by
    have h : i ∉ conflicts v := fun h => hi (Finset.mem_biUnion.mpr ⟨v,hv,h⟩)
    simpa [conflicts] using h
  have add (w : V) (hw : w = left i ∨ w = right i) : ¬ hit (insert w s) := by
    rintro ⟨a,ha,b,hb,e⟩
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · obtain ⟨h,k,_⟩ := e; omega
    · rcases hw with rfl | rfl
      · exact (clean b hb).2 e
      · have h := e.1; simp [right, Fin.natAdd] at h
    · rcases hw with rfl | rfl
      · have h := e.2.1; change 13 ≤ i.val at h; omega
      · exact (clean a ha).1 e
    · exact bad ⟨a,ha,b,hb,e⟩
  have avoids (w) (hw : w = left i ∨ w = right i) : w ∉ G := fun hg =>
    add w hw ((exactOn _).mpr ⟨mono (Finset.subset_insert _ _) hs,w,hg,Finset.mem_insert_self ..⟩)
  have ep : hit {left i, right i} := ⟨_,by simp,_,by simp,matching i⟩
  obtain ⟨v,hg,hv⟩ := ((exactOn _).mp ep).2
  exact avoids v (by simpa using hv) hg

theorem redundantGuard (H : Row → Prop) (mono : Monotone H) (G : Row)
    (exactOn : ∀ s, hit s ↔ H s ∧ ∃ v ∈ G, v ∈ s)
    (smallCertificates : ∀ s, H s → ∃ t ⊆ s, t.card ≤ 3 ∧ H t) :
    ∀ s, H s ↔ hit s := by
  intro s
  refine ⟨fun hs => ?_,fun e => ((exactOn s).mp e).1⟩
  obtain ⟨t,sub,sz,ht⟩ := smallCertificates s hs
  obtain ⟨a,ha,b,hb,ab⟩ := (unguardedSmall H mono G exactOn t sz).mp ht
  exact ⟨a,sub ha,b,sub hb,ab⟩

def fourPoints : Row := {0,1,3,9}
def lineInputs : Row := Finset.univ.filter (fun v => 13 ≤ v.val)
def relaxed (s : Row) : Prop := hit s ∨ fourPoints ⊆ s

theorem thresholdSharp : Monotone relaxed ∧
    (∀ s, hit s ↔ relaxed s ∧ ∃ v ∈ lineInputs, v ∈ s) ∧
    fourPoints.card = 4 ∧ relaxed fourPoints ∧ ¬ hit fourPoints := by
  have meets : ∀ b : V, 13 ≤ b.val → ∃ a ∈ fourPoints, edge a b := by decide +kernel
  refine ⟨?_,?_,by decide,Or.inr (Finset.Subset.refl _),?_⟩
  · intro s t sub h
    rcases h with ⟨a,ha,b,hb,e⟩ | h
    · exact Or.inl ⟨a,sub ha,b,sub hb,e⟩
    · exact Or.inr (h.trans sub)
  · intro s
    constructor
    · intro h
      obtain ⟨a,ha,b,hb,e⟩ := h
      exact ⟨Or.inl ⟨a,ha,b,hb,e⟩,b,by simpa [lineInputs] using e.2.1,hb⟩
    · rintro ⟨h,b,bl,hb⟩
      rcases h with h | h
      · exact h
      · obtain ⟨a,ha,e⟩ := meets b (by simpa [lineInputs] using bl)
        exact ⟨a,h ha,b,hb,e⟩
  · unfold hit; decide +kernel

end Guard650
#print axioms Guard650.unguardedSmall
#print axioms Guard650.redundantGuard
#print axioms Guard650.thresholdSharp
