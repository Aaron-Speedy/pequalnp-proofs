from pathlib import Path
d=Path('.pnp')
s=(d/'Tree4126.lean').read_text().split('  intro x\n  constructor',1)[1].split('def ds ',1)[0]
t='''import MergeWire4928
import PEqualNP.Outside.L_meta_7945
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity LocalFano4126
namespace Local4928
theorem fromBoundary (C : Circuit) (mono : Monotone2 C) (pos : Pos C) (neg : Neg C) :
    ∀ x, C.eval (List.ofFn x) = true ↔ F x := by
  intro x
  constructor'''+s+'''
def boundary (x : Fin 14 → Bool) := (∃ p l : Fin 7, Incident p l ∧
  x = fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) ∨
  (¬F x ∧ ∀ y, (∀ i, x i = true → y i = true) → x ≠ y → F y)

theorem separated (pre post : List Gate) (g : Gate) (out old : ℕ)
    (val : Valid ⟨pre ++ g :: post,out⟩) (ho : old < 14+pre.length) :
    ∃ x : Fin 14 → Bool, boundary x ∧
      (let w := pre.foldl wireStep (List.ofFn x); g.op.eval (g.inputs.map fun i => w.getD i false) ≠ w.getD old false) := by
  classical
  by_contra! same
  let C : Circuit := ⟨pre ++ g :: post,out⟩
  let D := eraseOne pre post 14 old out
  have keep (x : Fin 14 → Bool) (hb : boundary x) : C.eval (List.ofFn x) = D.eval (List.ofFn x) :=
    erasedEval pre post g 14 old out (List.ofFn x) (by simp) ho (same x hb)
  have monoC : Monotone2 C := by
    intro k hk
    obtain ⟨op,a,b,ins⟩ := shapeOf val.2.1 k hk
    exact ⟨by simpa using op,by simp [ins]⟩
  have monoD : Monotone2 D := by
    intro k hk
    change k ∈ pre ++ post.map (editGate (14+pre.length) old) at hk
    rcases List.mem_append.mp hk with h|h
    · exact monoC k (List.mem_append_left _ h)
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
      have orig := monoC z (List.mem_append_right _ (List.mem_cons_of_mem _ hz))
      simpa [editGate] using orig
  have yes : Pos D := by
    intro p l inc
    rw [← keep _ (Or.inl ⟨p,l,inc,rfl⟩)]
    exact (val.2.2 _).mpr ⟨p,l,inc,by simp,by simp⟩
  have no : Neg D := by
    intro x off maximal
    rw [← keep _ (Or.inr ⟨off,maximal⟩)]
    exact Bool.eq_false_iff.mpr (fun on => off ((val.2.2 _).mp on))
  have lower := PEqualNP.Outside.L_meta_7945.fano27 D monoD (fromBoundary D monoD yes no)
  have upper := val.1
  simp [D,eraseOne,Circuit.size] at lower upper
  omega
end Local4928
#print axioms Local4928.separated
'''
(d/'Distinct4928.lean').write_text(t)
