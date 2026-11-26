import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
namespace PEqualNP.Outside.Rename7893
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
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

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem transport : ∀ (C : Circuit) (w : ℕ) (σ : Fin 10 → Fin 10), Function.Injective σ → σ 0 = 0 →
      IsAO2 10 C → w ≠ 0 → w < 10+C.size →
      (∀ j g, 10+j ≤ w → C.gates[j]? = some g → 0 ∉ g.inputs) →
      ∃ (D : Circuit) (v : ℕ), IsAO2 10 D ∧ D.size = C.size ∧ v ≠ 0 ∧ v < 10+D.size ∧
        (∀ j g, 10+j ≤ v → D.gates[j]? = some g → 0 ∉ g.inputs) ∧
        ∀ x : Fin 10 → Bool, circuitFun 10 D x = circuitFun 10 C (x ∘ σ) ∧
          (D.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn (x ∘ σ))).getD w false := by
  intro C w σ inj fix ok nz lt reads
  let D := relabel 10 10 σ C
  let m := wmap 10 10 σ
  have small (i : ℕ) (h : i < 10) : m i < 10 := by simpa [m,wmap,h] using (σ ⟨i,h⟩).isLt
  have large (i : ℕ) (h : 10 ≤ i) : m i = i := by simp [m,wmap,Nat.not_lt.mpr h,Nat.sub_add_cancel h]
  have ne (i : ℕ) (h : i ≠ 0) : m i ≠ 0 := by
    by_cases hi : i < 10
    · intro eq
      have e : σ ⟨i,hi⟩ = σ 0 := by rw [fix]; apply Fin.ext; simpa [m,wmap,hi] using eq
      exact h (congrArg Fin.val (inj e))
    · rw [large i (by omega)]; exact h
  have bound (i j : ℕ) (hi : i < 10+j) : m i < 10+j := by
    by_cases h : i < 10
    · have := small i h; omega
    · rwa [large i (by omega)]
  have len : D.size = C.size := by simp [D,relabel,Circuit.size]
  refine ⟨D,m w,⟨?_,?_,?_⟩,len,ne _ nz,by rw [len]; exact bound w C.size lt,?_,?_⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ok.1 a ha
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [D,relabel] using hj
    change i ∈ (gateAt D j).inputs at hi
    unfold gateAt at hi
    rw [List.getD_eq_getElem D.gates _ hj] at hi
    simp only [D,relabel,List.getElem_map,relGate] at hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    apply bound
    apply ok.2.1 j hj' a
    unfold gateAt
    rw [List.getD_eq_getElem C.gates _ hj']
    exact ha
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using ok.2.2 a ha
  · intro j g hj hg hf
    have hj' : 10+j ≤ w := by
      by_cases h : w < 10
      · have := small w h; omega
      · rwa [large w (by omega)] at hj
    change (C.gates.map (relGate 10 10 σ))[j]? = some g at hg
    rw [List.getElem?_map] at hg
    cases he : C.gates[j]? with
    | none => simp [he] at hg
    | some a =>
      simp [he] at hg
      subst g
      obtain ⟨i,hi,eq⟩ := List.mem_map.mp hf
      exact ne i (fun h => reads j a hj' he (h ▸ hi)) eq
  · intro x
    have h := (rel_fold 10 10 σ C.gates _ _ (rel_init 10 10 σ x)).2.2
    exact ⟨h C.output,h w⟩
end PEqualNP.Outside.Rename7893
#print axioms PEqualNP.Outside.Rename7893.transport
