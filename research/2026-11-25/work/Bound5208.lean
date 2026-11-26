import Three5208
namespace SlotCount5208
theorem markedBound {n g : ℕ}
    (v : Fin (n+g) → Trace) (l r : Fin g → Fin (n+g)) (op : Fin g → Bool)
    (earlier : ∀ i, (l i).val < n+i.val ∧ (r i).val < n+i.val)
    (step : ∀ i, v (Fin.natAdd n i) = mix (op i) (v (l i)) (v (r i)))
    (inputs : ∀ q : Fin n, ¬ born (v (Fin.castAdd g q)))
    (two : (Finset.univ.filter fun q : Fin n => v (Fin.castAdd g q) 2 = true).card = 2)
    (used : ∀ w, v w 2 ≠ true → (∃ i, l i = w) ∨ ∃ i, r i = w)
    (out : ∃ i : Fin g, born (v (Fin.natAdd n i)))
    (j k : Fin g) (jk : j ≠ k)
    (jOn : v (l j) 2 = true ∧ v (r j) 2 = true)
    (kOn : v (l k) 2 = true ∧ v (r k) 2 = true)
    (jOff : v (l j) 0 = false ∧ v (r j) 0 = false)
    (kOff : v (l k) 1 = false ∧ v (r k) 1 = false) : n+1 ≤ g := by
  classical
  let S := Finset.univ.filter fun w => v w 2 = true
  let A := Finset.univ.filter fun i : Fin g => v (Fin.natAdd n i) 2 = true
  apply slotCount S A l r
  · unfold S A
    have count {m : ℕ} (f : Fin m → Bool) :
        (Finset.univ.filter fun i => f i = true).card =
          ∑ i : Fin m, (if f i = true then 1 else 0 : ℕ) := by
      exact (Finset.sum_boole (R := ℕ) (fun i => f i = true) Finset.univ).symm
    rw [count (fun w => v w 2),count (fun i => v (Fin.natAdd n i) 2)]
    rw [Fin.sum_univ_add]
    have eq := two
    rw [count (fun i => v (Fin.castAdd g i) 2)] at eq
    rw [eq]
  · intro w h
    exact used w (by simpa [S] using h)
  · intro i h
    have on : mix (op i) (v (l i)) (v (r i)) 2 = true := by
      simpa [A,step] using h
    have prop : ∀ (o : Bool) (p q : Trace), mix o p q 2 = true → p 2 = true ∨ q 2 = true := by decide
    simpa [S] using prop _ _ _ on
  · have prev (i : Fin g) (w : Fin (n+g)) (lt : w.val < n+i.val) (h : born (v w)) :
        ∃ a < i, born (mix (op a) (v (l a)) (v (r a))) := by
      revert lt h
      refine Fin.addCases (fun q _ h => False.elim (inputs q h)) (fun a lt h => ?_) w
      exact ⟨a,by change n+a.val < n+i.val at lt; exact Nat.lt_of_add_lt_add_left lt, (step a) ▸ h⟩
    have seq (i : Fin g) (t) (ht : t ∈ [v (l i),v (r i)]) (h : born t) :
        ∃ a < i, born (mix (op a) (v (l a)) (v (r a))) := by
      rcases (show t = v (l i) ∨ t = v (r i) by simpa using ht) with rfl | rfl
      · exact prev i _ (earlier i).1 h
      · exact prev i _ (earlier i).2 h
    simpa [S] using threeParents (fun i => v (l i)) (fun i => v (r i)) op seq
      (by simpa only [step] using out) j k jk jOn kOn jOff kOff
end SlotCount5208
#print axioms SlotCount5208.markedBound
