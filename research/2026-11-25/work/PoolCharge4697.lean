import Mathlib

namespace PoolCharge4697

variable {V : Type*} [DecidableEq V]
abbrev Pool (B : List (Finset V)) :=
  ∀ P a T, B = P ++ a :: T → ∃ b c : Finset V, a = b ∪ c ∧
    (b.card ≤ 1 ∨ b ∈ T) ∧ (c.card ≤ 1 ∨ c ∈ T)

def charges (B : List (Finset V)) (R : Finset V) :=
  (B.filter (fun a => decide (2 ≤ a.card ∧ a ⊆ R))).length

theorem covered (B : List (Finset V)) (R : Finset V) (small : R.card ≤ 3)
    (pool : Pool B) (ready : R.card ≤ 1 ∨ R ∈ B) :
    R.card ≤ charges B R + 1 := by
  induction B with
  | nil =>
    rcases ready with h | h
    · exact h
    · simp at h
  | cons a T ih =>
    have tail : Pool T := by
      intro P x S eq
      exact pool (a::P) x S (by simp [eq])
    by_cases tiny : R.card ≤ 1
    · exact tiny.trans (by omega)
    have mem := ready.resolve_left tiny
    have pos : 2 ≤ R.card := by omega
    by_cases old : R ∈ T
    · have bound := ih tail (Or.inr old)
      by_cases good : 2 ≤ a.card ∧ a ⊆ R
      · simp [charges,good] at bound ⊢; omega
      · simpa [charges,good] using bound
    · have eq := (List.mem_cons.mp mem).resolve_right old
      subst a
      obtain ⟨b,c,eq,br,cr⟩ := pool [] R T rfl
      have total := Finset.card_union_le b c
      rw [← eq] at total
      have first : 1 ≤ charges (R::T) R := by simp [charges,pos]
      by_cases three : 3 ≤ R.card
      · have child : ∃ x ∈ T, 2 ≤ x.card ∧ x ⊆ R := by
          by_cases hb : 2 ≤ b.card
          · exact ⟨b,br.resolve_left (by omega),hb,eq ▸ Finset.subset_union_left⟩
          · exact ⟨c,cr.resolve_left (by omega),by omega,eq ▸ Finset.subset_union_right⟩
        obtain ⟨x,xt,hx,sub⟩ := child
        have hx' : x ∈ T.filter (fun a => decide (2 ≤ a.card ∧ a ⊆ R)) :=
          List.mem_filter.mpr ⟨xt,by simp [hx,sub]⟩
        have nonempty := List.length_pos_of_mem hx'
        simp only [charges,List.filter_cons,Finset.Subset.refl,and_true,decide_eq_true pos,ite_true,List.length_cons] 
        omega
      · omega
end PoolCharge4697
#print axioms PoolCharge4697.covered
