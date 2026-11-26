import GraphBase
namespace PEqualNP.Outside.L_meta_612_aux
open PEqualNP.CircuitLowerBounds
abbrev MatchRow (m : ℕ) := Sum (Fin m → Bool) (Fin m)

def matchSample {m : ℕ} (r : MatchRow m) (v : Fin (m+m)) : Bool :=
  match r with
  | .inl choice => Fin.addCases (fun i => choice i) (fun i => !choice i) v
  | .inr j => Fin.addCases (fun i => decide (i = j)) (fun i => decide (i = j)) v

def matchTarget (m : ℕ) : Finset (MatchRow m) :=
  Finset.univ.image Sum.inl

theorem matchSeparation (m : ℕ) (a : MatchRow m) (_ha : a ∈ matchTarget m) (b : MatchRow m) (_hb : b ∈ matchTarget m) (ne : a ≠ b) :
    ¬ hull (inputBank (fun r i => !(matchSample r i))) {a,b} ⊆ matchTarget m := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ‹a ∈ matchTarget m›
  obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp ‹b ∈ matchTarget m›
  have diff : ∃ j, x j ≠ y j := by
    by_contra! same
    exact ne (congrArg Sum.inl (funext same))
  obtain ⟨j,hj⟩ := diff
  have separator : Sum.inr j ∈ hull (inputBank (fun r i => !(matchSample r i))) {Sum.inl x,Sum.inl y} := by
    apply memHull.mpr
    intro w hw sub
    rcases Finset.mem_insert.mp hw with rfl | input
    · have := sub (Finset.mem_insert_self _ _)
      simp at this
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp input
    have hx := sub (Finset.mem_insert_self _ _)
    have hy := sub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bool.not_eq_true'] at hx hy ⊢
    induction v using Fin.addCases with
    | left i =>
      simp [matchSample] at hx hy ⊢
      rintro rfl
      exact hj (hx.trans hy.symm)
    | right i =>
      simp only [matchSample,Fin.addCases_right,Bool.not_eq_false',decide_eq_false_iff_not] at hx hy ⊢
      rintro rfl
      exact hj (hx.trans hy.symm)
  intro bad
  simpa [matchTarget] using bad separator

theorem matchingAndCount {m : ℕ} (C : Circuit) (ok : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ r : MatchRow m, (!C.eval (List.ofFn (matchSample r))) = decide (r ∈ matchTarget m)) :
    m ≤ andCost C.gates := by
  have tested := circuitAndSearch (@matchSample m) C ok
  have eq : (Finset.univ.filter (fun r : MatchRow m => !C.eval (List.ofFn (matchSample r)))) = matchTarget m := by
    ext r; simp only [Finset.mem_filter,Finset.mem_univ,true_and,correct,decide_eq_true_eq]
  rw [eq] at tested
  have bound := separatedRows ((searchExact _ _ _).mp tested) (matchSeparation m)
  have card : (matchTarget m).card = 2 ^ m := by
    rw [matchTarget,Finset.card_image_of_injective _ Sum.inl_injective]
    simp
  rw [card] at bound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp bound
end PEqualNP.Outside.L_meta_612_aux
