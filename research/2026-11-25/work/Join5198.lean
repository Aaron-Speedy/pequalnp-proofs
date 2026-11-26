import MonoPin9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.GenericRejection
open PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.Join5198
def W (C : Circuit) (k : ℕ) (P L : Finset (Fin 13)) :=
  (C.wires (incidenceInput P L)).getD k false
def join (C : Circuit) (a b : ℕ) : Circuit := ⟨C.gates ++ [⟨.or,[a,b]⟩],26+C.size⟩
theorem size (C : Circuit) (a b : ℕ) : (join C a b).size=C.size+1 := by simp [join,Circuit.size]
theorem mono {C : Circuit} (h : Monotone2 C) (a b : ℕ) : Monotone2 (join C a b) := by
  intro gate hg
  change gate ∈ C.gates ++ [_] at hg
  rcases List.mem_append.mp hg with h'|h'
  · exact h _ h'
  · obtain rfl := List.mem_singleton.mp h'; simp

theorem eval (C : Circuit) (a b : ℕ) (P L : Finset (Fin 13)) :
    (join C a b).eval (incidenceInput P L) = (W C a P L || W C b P L) := by
  let xs := incidenceInput P L
  have len : (run C.gates xs).length = 26+C.size := by rw [run_length]; simp [xs,incidenceInput,Circuit.size]
  change (run (C.gates ++ [_]) xs).getD (26+C.size) false = _
  rw [run_snoc,← len,getD_snoc_eq]
  simp [GateOp.eval,W,run,xs,Circuit.wires]

theorem degree (C : Circuit) (a b : ℕ) (M : Finset ℕ) :
    (join C a b).lineDeg 26 M = max ((C.lineDegrees 26 M).getD a 0) ((C.lineDegrees 26 M).getD b 0) := by
  let step := fun (ws : List ℕ) (g : Gate) => ws ++ [g.lineDegree ws]
  have length (gs : List Gate) (ws : List ℕ) : (gs.foldl step ws).length = ws.length+gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have len : (C.lineDegrees 26 M).length = 26+C.size := by
    unfold Circuit.lineDegrees
    rw [show (fun (d : List ℕ) (g : Gate) => d ++ [g.lineDegree d]) = step from rfl,length]
    simp [Circuit.size]
  change ((C.gates ++ [_]).foldl step _).getD (26+C.size) 0 = _
  rw [List.foldl_append]
  change ((C.lineDegrees 26 M) ++ [_]).getD (26+C.size) 0 = _
  rw [← len,getD_snoc_eq]
  simp [Gate.lineDegree,step,Circuit.lineDegrees]
end PEqualNP.Outside.Join5198
#print axioms PEqualNP.Outside.Join5198.degree
