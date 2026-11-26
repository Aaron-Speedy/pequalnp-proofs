import CircuitAPart29

theorem counterexampleImpossible : ¬ (¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) := fun h => h PEqualNP.Outside.L_meta_16977
#print axioms counterexampleImpossible
