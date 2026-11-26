import MonoPin9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.Twins2056

theorem addOr {n s : ℕ} (g : (Fin n → Bool) → Bool) (i j : Fin n)
    (hc : MSize n g s) :
    MSize n (fun x => g (Function.update x j (x i || x j))) (s+1) := by
  let π : Fin n → Fin (n+1) := fun k => if k=j then Fin.last n else k.castSucc
  obtain ⟨D,ok,sz,ev⟩ := relabel_size π g s hc
  let gate : Gate := ⟨.or,[i.val,j.val]⟩
  let C : Circuit := ⟨gate::D.gates,D.output⟩
  refine ⟨C,?_,?_,?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · simp [gate]
    · exact ok a ha
  · simpa [C,Circuit.size] using Nat.add_le_add_right sz 1
  · intro x
    let y : Fin (n+1) → Bool := Fin.snoc (α := fun _ => Bool) x (x i || x j)
    have eq : y ∘ π = Function.update x j (x i || x j) := by
      funext k
      by_cases h : k=j
      · subst k; simp [y,π]
      · simp [y,π,h]
    have ws : step (List.ofFn x) gate = List.ofFn y := by
      rw [List.ofFn_succ']
      simp [step,gate,GateOp.eval,y,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    change (D.gates.foldl step (step (List.ofFn x) gate)).getD D.output false = _
    rw [ws]
    exact (ev y).trans (congrArg g eq)

theorem exactSaving {n s : ℕ} (f g : (Fin n → Bool) → Bool) (i j : Fin n)
    (a b u v : Fin n → Bool) (same : ∀ k, k ≠ i → a k = b k)
    (sensitive : f a ≠ f b) (nonconstant : g u ≠ g v)
    (restricts : ∀ x, f (Function.update x i false) = g x)
    (expands : ∀ x, g (Function.update x j (x i || x j)) = f x) :
    MSize n f (s+1) ↔ MSize n g s := by
  constructor
  · intro hf
    obtain ⟨t,ht,C,ok,sz,eval⟩ := pin f g i a b u v same sensitive nonconstant restricts hf
    exact ⟨C,ok,by omega,eval⟩
  · intro hg
    obtain ⟨C,ok,sz,eval⟩ := addOr g i j hg
    exact ⟨C,ok,sz,fun x => (eval x).trans (expands x)⟩
theorem mergeTwins {n s : ℕ} (f : (Fin n → Bool) → Bool) (i j : Fin n)
    (twins : ∀ x, f (Function.update (Function.update x j (x i || x j)) i false) = f x)
    (essential : ∃ a b, (∀ k, k ≠ i → a k = b k) ∧ f a ≠ f b) :
    MSize n f (s+1) ↔ MSize n (fun x => f (Function.update x i false)) s := by
  obtain ⟨a,b,same,neq⟩ := essential
  let u := Function.update a j (a i || a j)
  let v := Function.update b j (b i || b j)
  apply exactSaving f _ i j a b u v same neq _ (fun _ => rfl) twins
  intro eq
  exact neq ((twins a).symm.trans (eq.trans (twins b)))

end PEqualNP.Outside.Twins2056
#print axioms PEqualNP.Outside.Twins2056.exactSaving
#print axioms PEqualNP.Outside.Twins2056.mergeTwins
