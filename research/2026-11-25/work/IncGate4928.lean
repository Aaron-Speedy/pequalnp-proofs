import DistinctCore4928
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity LocalFano4126
namespace Local4928
theorem distinguishedInputs (lb : ∀ D : Circuit, Monotone2 D → (∀ x, D.eval (List.ofFn x) = true ↔ F x) → 27 ≤ D.size)
    (pre post : List Gate) (g : Gate) (out a b : ℕ) (val : Valid ⟨pre ++ g :: post,out⟩)
    (ins : g.inputs = [a,b]) (h : g.op = .and ∨ g.op = .or)
    (ha : a < 14+pre.length) (hb : b < 14+pre.length) (side : Bool) :
    ∃ x : Fin 14 → Bool, boundary x ∧
      (let w := pre.foldl wireStep (List.ofFn x); w.getD a false = side ∧ w.getD b false = !side) := by
  have sep (i : ℕ) (hi : i < 14+pre.length) := separatedUsing lb pre post g out i val hi
  have andLeft : ∀ u v : Bool, (u && v) ≠ u → u = true ∧ v = false := by decide
  have andRight : ∀ u v : Bool, (u && v) ≠ v → u = false ∧ v = true := by decide
  have orLeft : ∀ u v : Bool, (u || v) ≠ u → u = false ∧ v = true := by decide
  have orRight : ∀ u v : Bool, (u || v) ≠ v → u = true ∧ v = false := by decide
  rcases h with op|op <;> cases side
  · obtain ⟨x,bx,d⟩ := sep b hb
    exact ⟨x,bx,andRight _ _ (by simpa [ins,op,GateOp.eval] using d)⟩
  · obtain ⟨x,bx,d⟩ := sep a ha
    exact ⟨x,bx,andLeft _ _ (by simpa [ins,op,GateOp.eval] using d)⟩
  · obtain ⟨x,bx,d⟩ := sep a ha
    exact ⟨x,bx,orLeft _ _ (by simpa [ins,op,GateOp.eval] using d)⟩
  · obtain ⟨x,bx,d⟩ := sep b hb
    exact ⟨x,bx,orRight _ _ (by simpa [ins,op,GateOp.eval] using d)⟩
end Local4928
#print axioms Local4928.distinguishedInputs
