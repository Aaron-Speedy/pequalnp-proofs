import MonoPin9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.Plane9738
def ds (W : List ℕ) (g : Gate) := W ++ [g.lineDegree W]
def DegRel (n m : ℕ) (π : Fin n → Fin m) (W W' : List ℕ) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) 0 = W.getD w 0

theorem degree_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List ℕ) (g : Gate)
    (h : DegRel n m π W W') : DegRel n m π (ds W g) (ds W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have same : ((relGate n m π g).inputs.map fun i => W'.getD i 0) =
      g.inputs.map (fun i => W.getD i 0) := by
    simp only [relGate,List.map_map]
    apply List.map_congr_left
    intro a _
    exact h3 a
  have hv : (relGate n m π g).lineDegree W' = g.lineDegree W := by
    unfold Gate.lineDegree
    rw [same]
    rfl
  refine ⟨by simp [ds]; omega, by simp [ds]; omega, ?_⟩
  intro w
  simp only [ds, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem degree_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List ℕ, DegRel n m π W W' →
      DegRel n m π (gs.foldl ds W) ((gs.map (relGate n m π)).foldl ds W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (degree_step n m π W W' g h)


def emb (i : Fin 25) : Fin 26 := if h : i.val < 13 then i.castSucc else i.succ
def marks (n : ℕ) := Finset.Ico 13 n
def base (n : ℕ) := (List.range n).map (fun i => if i ∈ marks n then 1 else 0)
theorem dginit : DegRel 25 26 emb (base 25) (base 26) := by
  refine ⟨by decide, by decide, ?_⟩
  intro w
  by_cases hw : w < 25
  · have fin : ∀ i : Fin 25, (base 26).getD (emb i).val 0 = (base 25).getD i.val 0 := by decide
    simpa [wmap,hw] using fin ⟨w,hw⟩
  · have a : (base 25).length = 25 := by decide
    have b : (base 26).length = 26 := by decide
    simp only [wmap,dif_neg hw]
    rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
theorem lifted_degree (C : Circuit) :
    (relabel 25 26 emb C).lineDeg 26 (marks 26) = C.lineDeg 25 (marks 25) :=
  (degree_fold 25 26 emb C.gates _ _ dginit).2.2 C.output

end PEqualNP.Outside.Plane9738
#print axioms PEqualNP.Outside.Plane9738.lifted_degree
