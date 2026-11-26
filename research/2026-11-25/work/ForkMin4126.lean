import ForkPaths4126
open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3793
namespace LocalFano4126
namespace Attainment
def P (i : Fin 7) : Form := .lit (Fin.castAdd 7 i) true
def L (i : Fin 7) : Form := .lit (Fin.natAdd 7 i) true
def N (p : Fin 7) : Form := .or (.or (L p) (L (p-1))) (L (p-3))
def star (p : Fin 7) : Form := .and (P p) (N p)
def H : Form := .or (.or (.or (.or (.or (star 0) (star 1)) (star 3)) (star 4)) (star 5)) (star 6)
def left : Ctx := [(true,P 2)]
def right : Ctx := [(true,N 2)]
theorem starCorrect (p : Fin 7) (x : Fin 14 → Bool) :
    (star p).eval x = true ↔ ∃ l, Incident p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  have chart : ∀ p l : Fin 7, Incident p l ↔ l=p ∨ l=p-1 ∨ l=p-3 := by decide
  simp only [star,P,N,L,DMFormula.eval,ite_true,Bool.and_eq_true,Bool.or_eq_true]
  constructor
  · rintro ⟨hp,(h|h)|h⟩
    · exact ⟨p,(chart _ _).mpr (Or.inl rfl),hp,h⟩
    · exact ⟨p-1,(chart _ _).mpr (Or.inr (Or.inl rfl)),hp,h⟩
    · exact ⟨p-3,(chart _ _).mpr (Or.inr (Or.inr rfl)),hp,h⟩
  · rintro ⟨l,inc,hp,hl⟩
    rcases (chart _ _).mp inc with rfl | rfl | rfl
    · exact ⟨hp,Or.inl (Or.inl hl)⟩
    · exact ⟨hp,Or.inl (Or.inr hl)⟩
    · exact ⟨hp,Or.inr hl⟩
theorem attains (x) : RunFork [] left right false H x = true ↔ F x := by
  have law : ∀ u a b : Bool, ((u || a) && (u || b)) = (u || (a && b)) := by decide
  change ((H.eval x || (P 2).eval x) && (H.eval x || (N 2).eval x)) = true ↔ _
  rw [law]
  change (H.eval x || (star 2).eval x) = true ↔ _
  change _ ↔ ∃ p : Fin 7, ∃ l : Fin 7, Incident p l ∧ _ ∧ _
  simp_rw [← starCorrect]
  simp only [H,DMFormula.eval,Bool.or_eq_true]
  constructor
  · intro z
    rcases z with (((((h|h)|h)|h)|h)|h)|h
    all_goals exact ⟨_,h⟩
  · rintro ⟨p,h⟩
    fin_cases p <;> tauto
theorem cost : H.leaves + added left + added right + added [] = 28 := rfl
end Attainment
end LocalFano4126
#print axioms LocalFano4126.Attainment.attains
