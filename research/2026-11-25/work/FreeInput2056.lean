import MonoPin9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.FreeInput2056
def aux {n : ℕ} (a b : Fin n) (x : Fin n → Bool) : Fin (n+1) → Bool :=
  Fin.snoc (α := fun _ => Bool) x (x a || x b)
def Free {n : ℕ} (f : (Fin n → Bool) → Bool) (a b : Fin n) (s : ℕ) :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn (aux a b x)) = f x

theorem outside {m n s : ℕ} [Nonempty (Fin m)] (ι : Fin m → Fin n) (inj : Function.Injective ι)
    (g : (Fin m → Bool) → Bool) (a b : Fin n) (ha : a ∉ Set.range ι)
    (h : Free (fun x => g (x ∘ ι)) a b s) : MSize m g s := by
  classical
  let inv := Function.invFun ι
  have left : Function.LeftInverse inv ι := Function.leftInverse_invFun inj
  let π := Function.update inv a (inv b)
  have pi (k : Fin m) : π (ι k) = k := by
    have ne : ι k ≠ a := fun eq => ha ⟨k,eq⟩
    simpa [π,ne] using left k
  have same : π a = π b := by
    by_cases ab : a=b
    · rw [ab]
    · simp [π,Ne.symm ab]
  let ρ := Fin.snoc (α := fun _ => Fin m) π (π b)
  obtain ⟨C,cm,cs,ce⟩ := h
  obtain ⟨D,dm,ds,de⟩ := relabel_size ρ (fun y => C.eval (List.ofFn y)) s ⟨C,cm,cs,fun _ => rfl⟩
  refine ⟨D,dm,ds,fun x => (de x).trans ?_⟩
  have eq : x ∘ ρ = aux a b (x ∘ π) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [ρ,aux,Function.comp_def,same]
  change C.eval (List.ofFn (x ∘ ρ)) = g x
  rw [eq,ce]
  exact congrArg g (funext (fun j => congrArg x (pi j)))

theorem pay {n s : ℕ} {f : (Fin n → Bool) → Bool} {a b : Fin n}
    (h : Free f a b s) : MSize n f (s+1) := by
  obtain ⟨D,ok,sz,ev⟩ := h
  let gate : Gate := ⟨.or,[a.val,b.val]⟩
  let C : Circuit := ⟨gate::D.gates,D.output⟩
  refine ⟨C,?_,?_,?_⟩
  · intro k hk
    rcases List.mem_cons.mp hk with rfl|hk
    · simp [gate]
    · exact ok _ hk
  · simpa [C,Circuit.size] using Nat.add_le_add_right sz 1
  · intro x
    have ws : step (List.ofFn x) gate = List.ofFn (aux a b x) := by
      rw [List.ofFn_succ']
      simp [aux,step,gate,GateOp.eval,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    change (D.gates.foldl step (step (List.ofFn x) gate)).getD D.output false = _
    rw [ws]; exact ev x
end PEqualNP.Outside.FreeInput2056
#print axioms PEqualNP.Outside.FreeInput2056.outside
