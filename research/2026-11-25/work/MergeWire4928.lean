import Normalize4928
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Local4928
def wireStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def redirect (k old i : ℕ) := if i < k then i else if i = k then old else i-1
def editGate (k old : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (redirect k old)⟩
def eraseOne (pre post : List Gate) (n old out : ℕ) : Circuit :=
  let k := n+pre.length
  ⟨pre ++ post.map (editGate k old),redirect k old out⟩
theorem lengthRun (gs : List Gate) (w : List Bool) : (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih,wireStep]; omega

theorem suffixAgree (k old : ℕ) (earlier : old < k) (post : List Gate) (w z : List Bool)
    (offset : w.length = z.length+1) (range' : k ≤ z.length)
    (same : ∀ i, w.getD i false = z.getD (redirect k old i) false) :
    ∀ i, (post.foldl wireStep w).getD i false =
      ((post.map (editGate k old)).foldl wireStep z).getD (redirect k old i) false := by
  induction post generalizing w z with
  | nil => exact same
  | cons g gs ih =>
    have gate : g.op.eval (g.inputs.map fun i => w.getD i false) =
        (editGate k old g).op.eval ((editGate k old g).inputs.map fun i => z.getD i false) := by
      simp only [editGate,List.map_map,Function.comp_def]
      rw [show (fun i => w.getD i false) = (fun i => z.getD (redirect k old i) false) from funext same]
    apply ih (wireStep w g) (wireStep z (editGate k old g))
    · simp [wireStep,offset]
    · simp [wireStep]; omega
    · intro i
      unfold wireStep
      by_cases hi : i < w.length
      · have hj : redirect k old i < z.length := by unfold redirect; split <;> (first | omega | split <;> omega)
        rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ hj,same]
      · have hj : redirect k old i = i-1 := by unfold redirect; split <;> (first | omega | split <;> omega)
        rw [hj,List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),gate]
        congr 1 <;> omega

theorem erasedEval (pre post : List Gate) (g : Gate) (n old out : ℕ) (input : List Bool)
    (len : input.length = n) (oldLt : old < n+pre.length)
    (dup : let w := pre.foldl wireStep input; g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD old false) :
    (Circuit.mk (pre ++ g :: post) out).eval input = (eraseOne pre post n old out).eval input := by
  let w := pre.foldl wireStep input
  have size : w.length = n+pre.length := (lengthRun pre input).trans (by rw [len])
  change ((pre ++ g :: post).foldl wireStep input).getD out false =
    ((pre ++ post.map (editGate (n+pre.length) old)).foldl wireStep input).getD _ false
  rw [List.foldl_append,List.foldl_append,List.foldl_cons]
  apply suffixAgree _ old oldLt post (wireStep w g) w (by simp [wireStep]) (by omega) _ out
  intro i
  unfold wireStep
  by_cases h : i < n+pre.length
  · rw [List.getD_append _ _ _ _ (by omega)]; simp [redirect,h]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases eq : i = n+pre.length
    · subst i; simpa [redirect,size] using dup
    · have d : 1 ≤ i - w.length := by omega
      rw [List.getD_eq_default _ _ (by simpa using d)]
      symm
      apply List.getD_eq_default
      simp [redirect,h,eq,size]; omega
end Local4928
#print axioms Local4928.erasedEval
