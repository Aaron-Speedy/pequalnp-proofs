import DistinctCore4928
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity LocalFano4126
open PEqualNP.Outside.L_meta_5254_aux.RowStructure
namespace Local4928
abbrev Lower := ∀ D : Circuit, Monotone2 D → (∀ x, D.eval (List.ofFn x) = true ↔ F x) → 27 ≤ D.size
def positiveRow (x : Fin 14 → Bool) := ∃ p l : Fin 7, Incident p l ∧
  x = fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
def negativeRow (x : Fin 14 → Bool) := ¬F x ∧ ∀ y, (∀ i, x i = true → y i = true) → x ≠ y → F y
def prefixVals (pre : List Gate) (x : Fin 14 → Bool) := pre.foldl wireStep (List.ofFn x)
def valAt (pre : List Gate) (x : Fin 14 → Bool) (i : ℕ) := (prefixVals pre x).getD i false
def nextVal (pre : List Gate) (x : Fin 14 → Bool) (g : Gate) := g.op.eval (g.inputs.map (valAt pre x))

theorem compareGate (pre post : List Gate) (out : ℕ) (g h : Gate) (x : Fin 14 → Bool)
    (mono : ∀ k ∈ post, k.op = .and ∨ k.op = .or)
    (le : nextVal pre x g = true → nextVal pre x h = true) :
    (Circuit.mk (pre ++ g :: post) out).eval (List.ofFn x) = true →
    (Circuit.mk (pre ++ h :: post) out).eval (List.ofFn x) = true := by
  let w := prefixVals pre x
  change ((pre ++ g :: post).foldl wireStep (List.ofFn x)).getD out false = true → _
  change _ → ((pre ++ h :: post).foldl wireStep (List.ofFn x)).getD out false = true
  simp only [List.foldl_append,List.foldl_cons]
  apply wiresFrom_mono post mono (wireStep w g) (wireStep w h) (by simp [wireStep]) _ out
  intro i hi
  unfold wireStep at *
  by_cases small : i < w.length
  · simpa only [List.getD_append _ _ _ _ small] using hi
  · by_cases eq : i = w.length
    · subst i
      rw [getD_snoc_eq] at hi ⊢
      exact le hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      contradiction

theorem polarized (lb : Lower) (pre post : List Gate) (g : Gate) (out old : ℕ)
    (val : Valid ⟨pre ++ g :: post,out⟩) (ho : old < 14+pre.length) :
    (∃ x, positiveRow x ∧ nextVal pre x g = true ∧ valAt pre x old = false) ∨
    (∃ x, negativeRow x ∧ nextVal pre x g = false ∧ valAt pre x old = true) := by
  classical
  by_contra! bad
  let h : Gate := ⟨.or,[old]⟩
  let C : Circuit := ⟨pre ++ g :: post,out⟩
  let D := eraseOne pre post 14 old out
  have copy (x : Fin 14 → Bool) : nextVal pre x h = valAt pre x old := by simp [nextVal,h,GateOp.eval]
  have same (x : Fin 14 → Bool) : (Circuit.mk (pre ++ h :: post) out).eval (List.ofFn x) = D.eval (List.ofFn x) :=
    erasedEval pre post h 14 old out (List.ofFn x) (by simp) ho (copy x)
  have op (k) (hk : k ∈ post) : k.op = .and ∨ k.op = .or :=
    (shapeOf val.2.1 k (List.mem_append_right _ (List.mem_cons_of_mem _ hk))).1
  have mop (k) (hk : k ∈ C.gates) := shapeOf val.2.1 k hk
  have monoD : Monotone2 D := by
    intro k hk
    change k ∈ pre ++ post.map (editGate (14+pre.length) old) at hk
    rcases List.mem_append.mp hk with l|r
    · obtain ⟨op,a,b,ins⟩ := mop k (List.mem_append_left _ l)
      exact ⟨by simpa using op,by simp [ins]⟩
    · obtain ⟨k,hkpost,rfl⟩ := List.mem_map.mp r
      obtain ⟨op,a,b,ins⟩ := mop k (List.mem_append_right _ (List.mem_cons_of_mem _ hkpost))
      exact ⟨by simpa [editGate] using op,by simp [editGate,ins]⟩
  have yes : Pos D := by
    intro p l inc
    let x : Fin 14 → Bool := fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
    change D.eval (List.ofFn x) = true
    rw [← same]
    apply compareGate pre post out g h x op
    · intro on
      rw [copy]
      exact Bool.eq_true_of_not_eq_false (bad.1 x ⟨p,l,inc,rfl⟩ on)
    · exact (val.2.2 x).mpr ⟨p,l,inc,by simp [x],by simp [x]⟩
  have no : Neg D := by
    intro x off maximal
    apply Bool.eq_false_iff.mpr
    intro yes
    rw [← same] at yes
    have on := compareGate pre post out h g x op (fun hOn => by
      rw [copy] at hOn
      exact Bool.eq_true_of_not_eq_false (fun hOff => bad.2 x ⟨off,maximal⟩ hOff hOn)) yes
    exact off ((val.2.2 _).mp on)
  have lo := lb D monoD (fromBoundary D monoD yes no)
  have hi := val.1
  simp [D,eraseOne,Circuit.size] at hi lo
  omega
end Local4928
#print axioms Local4928.polarized
