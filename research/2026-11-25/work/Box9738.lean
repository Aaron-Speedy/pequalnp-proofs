import Mathlib
namespace PEqualNP.Outside.Boxes9738
abbrev P := Fin 13
abbrev L := Fin 12
def E : Finset (P × L) := {(0,3),(0,9),(0,11),(1,0),(1,4),(1,10),(2,0),(2,1),(2,5),(2,11),(3,1),(3,2),(3,6),(4,0),(4,2),(4,3),(4,7),(5,1),(5,3),(5,4),(5,8),(6,2),(6,4),(6,5),(6,9),(7,3),(7,5),(7,6),(7,10),(8,4),(8,6),(8,7),(8,11),(9,5),(9,7),(9,8),(10,0),(10,6),(10,8),(10,9),(11,1),(11,7),(11,9),(11,10),(12,2),(12,8),(12,10),(12,11)}
def matching (j : L) : P × L := (j.succ,j)
theorem nm (j : L) : matching j ∈ E := by revert j; decide +kernel
theorem nfour : ∀ a b : P, ∀ c d : L, (a,c) ∈ E → (a,d) ∈ E →
    (b,c) ∈ E → (b,d) ∈ E → a=b ∨ c=d := by decide +kernel
theorem sum_union {α : Type} [DecidableEq α] {k : ℕ} (T : Fin k → Finset α)
    (S : Finset α) (h : ∀ p ∈ S, ∃ t, p ∈ T t) : S.card ≤ ∑ t, (T t).card := by
  have sub : S ⊆ Finset.univ.biUnion T := by
    intro p hp
    obtain ⟨t,ht⟩ := h p hp
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,ht⟩
  exact (Finset.card_le_card sub).trans (Finset.card_biUnion_le)
theorem boxFormula {k : ℕ} (A : Fin k → Finset P) (B : Fin k → Finset L)
    (nonempty : ∀ t, (A t).Nonempty ∧ (B t).Nonempty)
    (sound : ∀ t, A t ×ˢ B t ⊆ E)
    (cover : ∀ p ∈ E, ∃ t, p ∈ A t ×ˢ B t) :
    60 ≤ ∑ t, ((A t).card + (B t).card) := by
  have tiny (t : Fin k) : (A t).card ≤ 1 ∨ (B t).card ≤ 1 := by
    by_contra! h
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp h.1
    obtain ⟨c,hc,d,hd,hcd⟩ := Finset.one_lt_card.mp h.2
    apply (nfour a b c d (sound t (Finset.mk_mem_product ha hc))
      (sound t (Finset.mk_mem_product ha hd)) (sound t (Finset.mk_mem_product hb hc))
      (sound t (Finset.mk_mem_product hb hd))).elim hab hcd
  have per (t : Fin k) : (A t ×ˢ B t).card + 1 ≤ (A t).card + (B t).card := by
    rw [Finset.card_product]
    have h := (nonempty t).1.card_pos
    have h' := (nonempty t).2.card_pos
    rcases tiny t with ha|hb
    · have : (A t).card = 1 := by omega
      simp [this,Nat.add_comm]
    · have : (B t).card = 1 := by omega
      simp [this]
  let D (t : Fin k) := Finset.univ.filter (fun j : L => matching j ∈ A t ×ˢ B t)
  have small (t : Fin k) : (D t).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    have h1 := Finset.mem_product.mp (Finset.mem_filter.mp hu).2
    have h2 := Finset.mem_product.mp (Finset.mem_filter.mp hv).2
    rcases tiny t with ha|hb
    · exact Fin.succ_injective _ (Finset.card_le_one.mp ha _ h1.1 _ h2.1)
    · exact Finset.card_le_one.mp hb _ h1.2 _ h2.2
  have diag := sum_union D Finset.univ (fun j _ => by
    obtain ⟨t,ht⟩ := cover (matching j) (nm j)
    exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩⟩)
  have kd := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => small t)
  have area := sum_union _ E cover
  have ub := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => per t)
  have sz : E.card = 48 := by decide
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at kd diag ub
  rw [Finset.sum_add_distrib]
  omega
end PEqualNP.Outside.Boxes9738
#print axioms PEqualNP.Outside.Boxes9738.boxFormula
