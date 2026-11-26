import Transversal5060
open PEqualNP.AndCount PEqualNP.Outside.L_meta_7533
namespace Local5060
theorem twoSlotsCross {C : AndCountCircuit 42} (hc : C.Computes plane) (out : C.outVars = ∅)
    {v : V} {s t : Slot C} (slots : positions C v = {s,t}) {a b : V}
    (ha : a ∈ (raw C s).erase v) (hb : b ∈ (raw C t).erase v) : plane.Adj a b := by
  classical
  by_contra miss
  let T : Finset V := {a,b}
  have ind : Independent T := by
    intro x hx y hy
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    all_goals first | exact plane.loopless.irrefl _ | exact miss | exact fun e => miss e.symm
  have hv : v ∉ T := by
    simp only [T,Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨(Finset.mem_erase.mp ha).1.symm,(Finset.mem_erase.mp hb).1.symm⟩
  have small : T.card ≤ 4 := (Finset.card_insert_le ..).trans (by simp)
  obtain ⟨r,hr,dis⟩ := missingSide hc out v T ind hv small
  rw [slots,Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with rfl|rfl
  · exact Finset.disjoint_left.mp dis (Finset.mem_erase.mp ha).2 (by simp [T])
  · exact Finset.disjoint_left.mp dis (Finset.mem_erase.mp hb).2 (by simp [T])
end Local5060
#print axioms Local5060.twoSlotsCross
