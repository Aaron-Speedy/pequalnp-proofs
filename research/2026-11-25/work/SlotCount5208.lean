import Mathlib
namespace SlotCount5208
open Finset
/-- Count the input slots available to read wires that are off on one row. -/
theorem slotCount {n g : ℕ} (on : Finset (Fin (n+g))) (active : Finset (Fin g))
    (left right : Fin g → Fin (n+g))
    (inputCount : on.card = 2 + active.card)
    (used : ∀ w ∉ on, (∃ i, left i = w) ∨ ∃ i, right i = w)
    (gates : ∀ i ∈ active, left i ∈ on ∨ right i ∈ on)
    (three : 3 ≤ (univ.filter fun i => left i ∈ on ∧ right i ∈ on).card) :
    n+1 ≤ g := by
  classical
  let L := univ.filter fun i => left i ∈ on
  let R := univ.filter fun i => right i ∈ on
  have covers : active ⊆ L ∪ R := by
    intro i hi
    simpa [L,R] using gates i hi
  have same : L ∩ R = univ.filter fun i => left i ∈ on ∧ right i ∈ on := by
    ext i; simp [L,R]
  have slots := card_union_add_card_inter L R
  have enough := card_le_card covers
  have off : onᶜ ⊆ (Lᶜ.image left) ∪ (Rᶜ.image right) := by
    intro w hw
    have no := mem_compl.mp hw
    rcases used w no with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact mem_union_left _ (mem_image.mpr ⟨i,by simpa [L] using no,rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨i,by simpa [R] using no,rfl⟩)
  have bound := calc
    onᶜ.card ≤ ((Lᶜ.image left) ∪ (Rᶜ.image right)).card := card_le_card off
    _ ≤ (Lᶜ.image left).card + (Rᶜ.image right).card := card_union_le _ _
    _ ≤ Lᶜ.card + Rᶜ.card := Nat.add_le_add card_image_le card_image_le
  have a := card_add_card_compl on
  have b := card_add_card_compl L
  have c := card_add_card_compl R
  simp only [Fintype.card_fin] at a b c
  rw [same] at slots
  omega
end SlotCount5208
#print axioms SlotCount5208.slotCount
