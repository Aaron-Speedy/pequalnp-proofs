import Observations4928
namespace Features4928
abbrev Token := V ⊕ Finset V
def observe (P U : Finset V) : Token → Prop
  | .inl p => p ∈ P
  | .inr t => hit t U
def edgeOn (P U : Finset V) := ∃ p ∈ P, hit (linesAt p) U
def enough (reads : List Token) := ∀ P U Q W : Finset V,
  (∀ t ∈ reads, observe P U t ↔ observe Q W t) → (edgeOn P U ↔ edgeOn Q W)

theorem interfaceClassification (reads : List Token) (ok : enough reads) :
    14 ≤ reads.length ∧ (reads.length ≤ 14 → reads.Nodup ∧
      (reads.toFinset.toRight = Finset.univ.image (fun l : V => ({l} : Finset V)) ∨
       reads.toFinset.toRight = Finset.univ.image linesAt)) := by
  classical
  have every : reads.toFinset.toLeft = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro p
    by_contra miss
    have sameness : ∀ t ∈ reads, observe {p} Finset.univ t ↔ observe ∅ Finset.univ t := by
      intro t ht
      cases t with
      | inr t => rfl
      | inl q =>
        have nq : q ≠ p := by rintro rfl; exact miss (Finset.mem_toLeft.mpr (List.mem_toFinset.mpr ht))
        simp [observe,nq]
    have pos : edgeOn {p} Finset.univ := ⟨p,by simp,p,by simp [linesAt,LocalFano4126.Incident],by simp⟩
    have neg := (ok _ _ _ _ sameness).mp pos
    simpa [edgeOn] using neg
  have det : Determines reads.toFinset.toRight := by
    intro p u v h
    have e := ok {p} u {p} v (by
      intro t ht
      cases t with
      | inl q => rfl
      | inr t => exact h t (Finset.mem_toRight.mpr (List.mem_toFinset.mpr ht)))
    simpa [edgeOn] using e
  obtain ⟨seven,shape⟩ := minimumObservations det
  have partition := Finset.card_toLeft_add_card_toRight (u := reads.toFinset)
  rw [every] at partition
  have sevenPts : (Finset.univ : Finset V).card = 7 := by decide
  rw [sevenPts] at partition
  have bound := reads.toFinset_card_le
  refine ⟨by omega,fun small => ⟨?_,shape (by omega)⟩⟩
  apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (reads : Multiset Token))).mp
  change reads.toFinset.card = reads.length
  omega
end Features4928
#print axioms Features4928.interfaceClassification
