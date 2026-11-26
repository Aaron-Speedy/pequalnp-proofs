import Trail9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.Plane9738
def ext (B : Circuit) : Circuit :=
  ⟨B.gates ++ trail (26+B.size) B.output, 26+B.size+4⟩
theorem ext_size (B : Circuit) : (ext B).size = B.size + 5 := by simp [ext,trail,Circuit.size]
theorem ext_mono (B : Circuit) (h : Monotone2 B) : Monotone2 (ext B) := by
  intro g mem
  rcases List.mem_append.mp mem with h'|h'
  · exact h _ h'
  · simp only [trail,List.mem_cons,List.not_mem_nil,or_false] at h'
    rcases h' with rfl|rfl|rfl|rfl|rfl <;> simp
theorem lift_mono (C : Circuit) (h : Monotone2 C) : Monotone2 (relabel 25 26 emb C) := by
  intro g mem
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp mem
  exact ⟨(h old ho).1,by simpa [relGate] using (h old ho).2⟩
theorem lift_eval (C : Circuit) (x : Fin 26 → Bool) :
    (relabel 25 26 emb C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ emb)) :=
  (rel_fold 25 26 emb C.gates _ _ (rel_init _ _ emb x)).2.2 C.output
theorem ext_eval (B : Circuit) (h : B.output < 26+B.size) (x : Fin 26 → Bool) :
    (ext B).eval (List.ofFn x) =
      (B.eval (List.ofFn x) || (x 13 && ((x 0 || x 1) || (x 3 || x 9)))) := by
  let W := run B.gates (List.ofFn x)
  have len : W.length = 26+B.size := by simp [W,run_length,Circuit.size]
  have old (i : Fin 26) : W.getD i.val false = x i := by
    rw [show W = run B.gates (List.ofFn x) from rfl,run_input _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have t := trailVal false (· || ·) (· && ·) step
    (by intro w i j; simp [step,GateOp.eval]) (by intro w i j; simp [step,GateOp.eval])
    W B.output (by omega) (by omega)
  rw [len] at t
  change ((B.gates ++ trail (26+B.size) B.output).foldl step (List.ofFn x)).getD _ _ = _
  rw [List.foldl_append]
  have h0 : W.getD 0 false = x 0 := old 0
  have h1 : W.getD 1 false = x 1 := old 1
  have h3 : W.getD 3 false = x 3 := old 3
  have h9 : W.getD 9 false = x 9 := old 9
  have h13 : W.getD 13 false = x 13 := old 13
  rw [h0,h1,h3,h9,h13] at t
  exact t
theorem ds_len (g : List Gate) (x : List ℕ) : (g.foldl ds x).length = x.length+g.length := by
  induction g generalizing x with
  | nil => simp
  | cons h t ih => simp [ih,ds]; omega
theorem ds_input (g : List Gate) (x : List ℕ) (i : ℕ) (h : i<x.length) :
    (g.foldl ds x).getD i 0 = x.getD i 0 := by
  induction g generalizing x with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldl_cons,ih _ (by simp [ds]; omega)]
    exact List.getD_append _ _ _ _ h
theorem ext_deg (B : Circuit) (h : B.output < 26+B.size) :
    (ext B).lineDeg 26 (marks 26) = max (B.lineDeg 26 (marks 26)) 1 := by
  let W := B.gates.foldl ds (base 26)
  have len : W.length = 26+B.size := by simp [W,ds_len,base,Circuit.size]
  have old (i : Fin 26) : W.getD i.val 0 = (base 26).getD i.val 0 :=
    ds_input _ _ _ (by simp [base])
  have t := trailVal 0 max (· + ·) ds
    (by intro w i j; simp [ds,Gate.lineDegree]) (by intro w i j; simp [ds,Gate.lineDegree])
    W B.output (by omega) (by omega)
  rw [len] at t
  change ((B.gates ++ trail (26+B.size) B.output).foldl ds (base 26)).getD _ _ = _
  rw [List.foldl_append]
  have h0 : W.getD 0 0 = 0 := old 0
  have h1 : W.getD 1 0 = 0 := old 1
  have h3 : W.getD 3 0 = 0 := old 3
  have h9 : W.getD 9 0 = 0 := old 9
  have h13 : W.getD 13 0 = 1 := old 13
  rw [h0,h1,h3,h9,h13] at t
  exact t
end PEqualNP.Outside.Plane9738
