import Features4928
open LocalFano4126
namespace Features4928
def hit (t u : Finset V) := ∃ i ∈ t, i ∈ u
def Determines (tokens : Finset (Finset V)) := ∀ p u v,
  (∀ t ∈ tokens, hit t u ↔ hit t v) → (hit (linesAt p) u ↔ hit (linesAt p) v)

theorem determines_iff {tokens : Finset (Finset V)} : Determines tokens ↔ Covers tokens := by
  classical
  constructor
  · intro det z hz
    obtain ⟨p,l⟩ := z
    have inc : Incident p l := by simpa [flags] using hz
    have hl : l ∈ linesAt p := by simpa [linesAt] using inc
    let u := (linesAt p)ᶜ
    let v := insert l u
    have no : ¬ hit (linesAt p) u := by rintro ⟨i,hi,hm⟩; exact Finset.mem_compl.mp hm hi
    have yes : hit (linesAt p) v := ⟨l,hl,Finset.mem_insert_self ..⟩
    by_contra! bad
    apply no ((det p u v ?_).mpr yes)
    intro t ht
    constructor
    · rintro ⟨i,hi,hu⟩
      exact ⟨i,hi,Finset.mem_insert_of_mem hu⟩
    · rintro ⟨i,hi,hm⟩
      rcases Finset.mem_insert.mp hm with rfl|hu
      · by_contra untouched
        have sub : t ⊆ linesAt p := by
          intro j hj
          by_contra miss
          exact untouched ⟨j,hj,Finset.mem_compl.mpr miss⟩
        exact bad t ht (Finset.mem_filter.mpr ⟨hz,hi,sub⟩)
      · exact ⟨i,hi,hu⟩
  · intro cov p u v same
    have one (a b : Finset V) (h : ∀ t ∈ tokens, hit t a → hit t b) :
        hit (linesAt p) a → hit (linesAt p) b := by
      rintro ⟨l,hl,ha⟩
      have inc : Incident p l := by simpa [linesAt] using hl
      obtain ⟨t,ht,good⟩ := cov (p,l) (by simpa [flags] using inc)
      obtain ⟨mem,sub⟩ := (Finset.mem_filter.mp good).2
      obtain ⟨i,hi,hb⟩ := h t ht ⟨l,mem,ha⟩
      exact ⟨i,sub hi,hb⟩
    exact ⟨one u v fun t ht => (same t ht).mp,one v u fun t ht => (same t ht).mpr⟩

theorem minimumObservations {tokens : Finset (Finset V)} (det : Determines tokens) :
    7 ≤ tokens.card ∧ (tokens.card = 7 →
      tokens = Finset.univ.image (fun l : V => ({l} : Finset V)) ∨ tokens = Finset.univ.image linesAt) :=
  ⟨seven (determines_iff.mp det),fun eq => rigid (determines_iff.mp det) eq.le⟩
end Features4928
#print axioms Features4928.minimumObservations
