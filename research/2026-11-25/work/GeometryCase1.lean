import CapCase1
namespace CapCase1
open PEqualNP.MetaComplexity SignedRect4126

def incidence (x : Fin 14 → Bool) : Bool :=
  decide (∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

def liftInputs (x : Fin 14 → Bool) : Fin 15 → Bool :=
  Fin.lastCases ((x 0 || x 1) && x 7) x

theorem rowInputs : ∀ p i, liftInputs (fun j => X p j.castSucc) i = X p i := by decide +kernel
theorem colInputs : ∀ q i, liftInputs (fun j => Y q j.castSucc) i = Y q i := by decide +kernel
theorem rowYes : ∀ p, incidence (fun j => X p j.castSucc) = true := by decide +kernel
theorem colNo : ∀ q, incidence (fun j => Y q j.castSucc) = false := by decide +kernel

theorem needs27Leaves (f : DMFormula 15) (pf : pos f) (used : 2 ≤ occurrences 14 f)
    (computes : ∀ x, f.eval (liftInputs x) = incidence x) : 27 ≤ f.leaves := by
  by_contra! small
  apply excludes f pf (by omega) used
  · intro p
    have e := computes (fun j => X p j.castSucc)
    rwa [show liftInputs (fun j => X p j.castSucc) = X p from funext (rowInputs p),rowYes] at e
  · intro q
    have e := computes (fun j => Y q j.castSucc)
    rwa [show liftInputs (fun j => Y q j.castSucc) = Y q from funext (colInputs q),colNo] at e
end CapCase1
#print axioms CapCase1.needs27Leaves
