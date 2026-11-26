import GateChart4928
open PEqualNP.CircuitLowerBounds LocalFano4126
namespace Local4928
def references (gs : List Gate) (out : ℕ) := out :: gs.flatMap Gate.inputs
theorem readSupport (gs : List Gate) (out : ℕ) (w z : List Bool) (len : w.length=z.length)
    (h : ∀ i ∈ references gs out, i < w.length → w.getD i false = z.getD i false) :
    (gs.foldl wireStep w).getD out false = (gs.foldl wireStep z).getD out false := by
  induction gs generalizing w z with
  | nil =>
    by_cases ok : out < w.length
    · exact h out (by simp [references]) ok
    · exact (List.getD_eq_default w false (show w.length ≤ out by omega)).trans (List.getD_eq_default z false (by omega)).symm
  | cons g gs ih =>
    have left {i} (hi : i ∈ g.inputs) : i ∈ references (g::gs) out := by
      simp [references,hi]
    have rest {i} (hi : i ∈ references gs out) : i ∈ references (g::gs) out := by
      simpa [references] using (show i = out ∨ i ∈ g.inputs ∨ i ∈ gs.flatMap Gate.inputs from
        (List.mem_cons.mp hi).imp_right Or.inr)
    have newBit : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => z.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      by_cases ok : i < w.length
      · exact h i (left hi) ok
      · exact (List.getD_eq_default w false (show w.length ≤ i by omega)).trans (List.getD_eq_default z false (by omega)).symm
    apply ih (wireStep w g) (wireStep z g) (by simp [wireStep,len])
    intro i hi live
    unfold wireStep
    by_cases ok : i < w.length
    · rw [List.getD_append _ _ _ _ ok,List.getD_append _ _ _ _ (by omega)]
      exact h i (rest hi) ok
    · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len,newBit]

theorem allRead (pre post : List Gate) (g : Gate) (out : ℕ)
    (val : Valid ⟨pre ++ g :: post,out⟩) : 14+pre.length ∈ references post out := by
  by_contra unused
  let D := eraseOne pre post 14 0 out
  let C : Circuit := ⟨pre ++ g :: post,out⟩
  let h : Gate := ⟨.or,[0]⟩
  have mono : PEqualNP.MetaComplexity.Monotone2 D := by
    intro t ht
    change t ∈ pre ++ post.map (editGate (14+pre.length) 0) at ht
    rcases List.mem_append.mp ht with hp|hp
    · obtain ⟨op,a,b,ins⟩ := shapeOf val.2.1 t (List.mem_append_left _ hp)
      exact ⟨by simpa using op,by simp [ins]⟩
    · obtain ⟨t,htpost,rfl⟩ := List.mem_map.mp hp
      obtain ⟨op,a,b,ins⟩ := shapeOf val.2.1 t (List.mem_append_right _ (List.mem_cons_of_mem _ htpost))
      exact ⟨by simpa [editGate] using op,by simp [editGate,ins]⟩
  have same (x : Fin 14 → Bool) : C.eval (List.ofFn x) = D.eval (List.ofFn x) := by
    have e := erasedEval pre post h 14 0 out (List.ofFn x) (by simp) (by omega)
      (by simp [h,GateOp.eval])
    rw [← e]
    change ((pre ++ g::post).foldl wireStep (List.ofFn x)).getD out false =
      ((pre ++ h::post).foldl wireStep (List.ofFn x)).getD out false
    simp only [List.foldl_append,List.foldl_cons]
    let w := pre.foldl wireStep (List.ofFn x)
    have size : w.length = 14+pre.length := (lengthRun ..).trans (by simp)
    apply readSupport post out (wireStep w g) (wireStep w h) (by simp [wireStep])
    intro i hi bound
    have ne : i ≠ 14+pre.length := fun eq => unused (eq ▸ hi)
    simp only [wireStep,List.length_append,List.length_singleton] at bound
    have ok : i < w.length := by omega
    unfold wireStep
    rw [List.getD_append _ _ _ _ ok,List.getD_append _ _ _ _ ok]
  have lb := PEqualNP.Outside.L_meta_7945.fano27 D mono (fun x => (same x ▸ val.2.2 x))
  have small := val.1
  simp [C,D,eraseOne,Circuit.size] at lb small
  omega
end Local4928
#print axioms Local4928.allRead
