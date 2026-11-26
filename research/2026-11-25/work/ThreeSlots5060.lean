import TwoSlots5060
open PEqualNP.AndCount PEqualNP.Outside.L_meta_7533
namespace Local5060

theorem crossSmall (A B : Finset V) (h : ∀ a ∈ A, ∀ b ∈ B, plane.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases small : A.card ≤ 1
  · exact Or.inl small
  obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  exact Or.inr ((Finset.card_le_card (show B ⊆ neighbors x ∩ neighbors y from fun b hb =>
    Finset.mem_inter.mpr ⟨mem_neighbors.mpr (h x hx b hb),mem_neighbors.mpr (h y hy b hb)⟩)).trans (intersections x y ne))

theorem thinAlternate {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    {v m : V} {s t u : Slot C} (covered : positions C v ⊆ {s,t,u})
    (hm : m ∈ (raw C s).erase v) :
    (((raw C t).erase v) \ neighbors m).card ≤ 1 ∨
    (((raw C u).erase v) \ neighbors m).card ≤ 1 := by
  apply crossSmall
  intro a ha b hb
  obtain ⟨ha,am⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨hb,bm⟩ := Finset.mem_sdiff.mp hb
  have am' : ¬ plane.Adj m a := fun e => am (mem_neighbors.mpr e)
  have bm' : ¬ plane.Adj m b := fun e => bm (mem_neighbors.mpr e)
  by_contra miss
  let T : Finset V := {m,a,b}
  have ind : Independent T := by
    intro x hx y hy
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl
    all_goals first | exact plane.loopless.irrefl _ | assumption | exact fun e => am' e.symm | exact fun e => bm' e.symm | exact fun e => miss e.symm
  have hv : v ∉ T := by
    simp only [T,Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨(Finset.mem_erase.mp hm).1.symm,(Finset.mem_erase.mp ha).1.symm,(Finset.mem_erase.mp hb).1.symm⟩
  have small : T.card ≤ 4 := by
    have h := Finset.card_insert_le m ({a,b} : Finset V)
    have g := Finset.card_insert_le a ({b} : Finset V)
    dsimp [T]; simp only [Finset.card_singleton] at g; omega
  obtain ⟨r,hr,dis⟩ := missingSide hc out v T ind hv small
  have cases' := covered hr
  simp only [Finset.mem_insert,Finset.mem_singleton] at cases'
  rcases cases' with rfl|rfl|rfl
  · exact Finset.disjoint_left.mp dis (Finset.mem_erase.mp hm).2 (by simp [T])
  · exact Finset.disjoint_left.mp dis (Finset.mem_erase.mp ha).2 (by simp [T])
  · exact Finset.disjoint_left.mp dis (Finset.mem_erase.mp hb).2 (by simp [T])
end Local5060
#print axioms Local5060.thinAlternate
