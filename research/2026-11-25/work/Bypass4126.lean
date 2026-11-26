import SharedFork4126
open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3793
namespace LocalFano4126
def jump (root : Bool) (v : Option Form) (p : Bool × Form) : Option Form :=
  match v with
  | none => if p.1 = root then some p.2 else none
  | some f => some (branch p.1 f p.2)
def optionEval (root : Bool) (v : Option Form) (x : Fin 14 → Bool) :=
  v.elim (!root) (fun f => f.eval x)
def mass (v : Option Form) := v.elim 0 DMFormula.leaves
def optPos (v : Option Form) := ∀ f ∈ v, Positive f
theorem evalJump (root : Bool) (v : Option Form) (p : Bool × Form) (x) :
    optionEval root (jump root v p) x = bval p.1 (optionEval root v x) (p.2.eval x) := by
  rcases p with ⟨op,f⟩
  cases v with
  | none => cases root <;> cases op <;> cases e : f.eval x <;> simp [jump,optionEval,bval,e]
  | some g => exact branchEval op g f x
theorem boundJump (root : Bool) (v : Option Form) (p : Bool × Form) :
    mass (jump root v p) ≤ mass v + p.2.leaves := by
  cases v with
  | none => by_cases e : p.1 = root <;> simp [jump,mass,e]
  | some f => simp [jump,mass,branchLeaves]
theorem posJump (root : Bool) (v : Option Form) (p : Bool × Form) (pv : optPos v) (pp : Positive p.2) :
    optPos (jump root v p) := by
  cases v with
  | none => by_cases e : p.1 = root <;> simpa [jump,optPos,e] using (by assumption : Positive p.2) <;> trivial
  | some f =>
    simp only [optPos, Option.mem_def, Option.some.injEq, forall_eq] at pv
    simpa [optPos,jump] using branchPos p.1 (pv f rfl) pp
theorem chain (c : Ctx) (root : Bool) (v : Option Form) (pc : ∀ p ∈ c, Positive p.2) (pv : optPos v) :
    let t := c.foldl (jump root) v
    (∀ x, optionEval root t x = evalCtx c x (optionEval root v x)) ∧
    mass t ≤ mass v + added c ∧ optPos t := by
  induction c generalizing v with
  | nil => exact ⟨fun _ => rfl,by simp [added],pv⟩
  | cons p c ih =>
    obtain ⟨e,b,good⟩ := ih (jump root v p) (fun q hq => pc q (by simp [hq])) (posJump _ _ _ pv (pc p (by simp)))
    refine ⟨fun x => (e x).trans (by rw [evalJump]; rfl),?_,good⟩
    change mass (c.foldl (jump root) (jump root v p)) ≤ mass v + added (p::c)
    have h := boundJump root v p
    simp only [added,List.map_cons,List.sum_cons] at b ⊢; omega
theorem directPathFloor (outer inner : Ctx) (root : Bool) (h : Form)
    (ph : Positive h) (pi : ∀ p ∈ inner, Positive p.2) (po : ∀ p ∈ outer, Positive p.2)
    (correct : ∀ x, evalCtx outer x (bval root (h.eval x) (evalCtx inner x (h.eval x))) = true ↔ F x) :
    28 ≤ h.leaves + added inner + added outer := by
  let t := inner.foldl (jump root) none
  obtain ⟨eq,b,p⟩ := chain inner root none pi (by simp [optPos])
  change mass t ≤ 0 + added inner at b
  change optPos t at p
  change ∀ x, optionEval root t x = evalCtx inner x (!root) at eq
  let f := t.elim h (branch root h)
  have pos : Positive f := by
    cases e : t with
    | none => simpa [f,e] using ph
    | some s => simpa [f,e] using branchPos root ph (p s (by simp [e]))
  have sem (x) : f.eval x = bval root (h.eval x) (evalCtx inner x (h.eval x)) := by
    have key : bval root (h.eval x) (evalCtx inner x (!root)) =
        bval root (h.eval x) (evalCtx inner x (h.eval x)) := by cases root <;> cases h.eval x <;> rfl
    rw [← key,← eq]
    cases e : t with
    | none => cases root <;> cases u : h.eval x <;> simp [f,e,optionEval,bval,u]
    | some s => simpa [f,e,optionEval] using branchEval root h s x
  have lower := formulaFloor (plug outer f) (plugPos _ _ pos po) (fun x => by rw [plugEval,sem]; exact correct x)
  rw [plugLeaves] at lower
  cases e : t with
  | none => simp [f,e] at lower; omega
  | some s => simp [f,e,branchLeaves] at lower; simp [mass,e] at b; omega
end LocalFano4126
#print axioms LocalFano4126.directPathFloor
