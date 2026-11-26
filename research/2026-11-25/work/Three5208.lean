import SlotCount5208
namespace SlotCount5208
abbrev Trace := Fin 3 → Bool
abbrev born (t : Trace) := t 0 = false ∧ t 1 = false ∧ t 2 = true
abbrev mix (disj : Bool) (a b : Trace) : Trace := fun i => bif disj then a i || b i else a i && b i
theorem newPair : ∀ (op : Bool) (a b : Trace), ¬ born a → ¬ born b → born (mix op a b) →
    (a 2 = true ∧ b 2 = true) ∧ (a 0 = true ∨ b 0 = true) ∧ (a 1 = true ∨ b 1 = true) := by decide +kernel

theorem threeParents {g : ℕ} (a b : Fin g → Trace) (op : Fin g → Bool)
    (ordered : ∀ i, ∀ t ∈ [a i,b i], born t → ∃ j < i, born (mix (op j) (a j) (b j)))
    (out : ∃ i, born (mix (op i) (a i) (b i)))
    (j k : Fin g) (jk : j ≠ k)
    (jOn : a j 2 = true ∧ b j 2 = true) (kOn : a k 2 = true ∧ b k 2 = true)
    (jOff : a j 0 = false ∧ b j 0 = false) (kOff : a k 1 = false ∧ b k 1 = false) :
    3 ≤ (Finset.univ.filter fun i => a i 2 = true ∧ b i 2 = true).card := by
  classical
  let s := Finset.univ.filter fun i => born (mix (op i) (a i) (b i))
  have ne : s.Nonempty := by simpa [s,Finset.Nonempty] using out
  let m := s.min' ne
  have hm : born (mix (op m) (a m) (b m)) := (Finset.mem_filter.mp (s.min'_mem ne)).2
  have clean (t) (ht : t ∈ [a m,b m]) : ¬ born t := by
    intro bt
    obtain ⟨i,lt,h⟩ := ordered m t ht bt
    have ge := s.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    exact (not_lt_of_ge ge) lt
  obtain ⟨on,one,two⟩ := newPair _ _ _ (clean _ (by simp)) (clean _ (by simp)) hm
  have mj : m ≠ j := by rintro rfl; simp [jOff.1,jOff.2] at one
  have mk : m ≠ k := by rintro rfl; simp [kOff.1,kOff.2] at two
  have sub : ({m,j,k} : Finset _) ⊆ Finset.univ.filter (fun i => a i 2 = true ∧ b i 2 = true) := by
    intro i hi
    rcases (show i = m ∨ i = j ∨ i = k by simpa using hi) with rfl | rfl | rfl
    all_goals exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by assumption⟩
  simpa [mj,mk,jk] using Finset.card_le_card sub
end SlotCount5208
#print axioms SlotCount5208.threeParents
