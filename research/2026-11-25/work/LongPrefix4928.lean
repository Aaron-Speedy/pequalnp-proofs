import DegreeBudget4928
open Features4928 LocalFano4126 PEqualNP.CircuitLowerBounds
namespace Local4928
def Isolated (d : List ℕ) (p : ℕ) := ∀ i, d.getD i 0 ≤ if i=p then 1 else 0
theorem untouched (pre : List Gate) (p : ℕ) (avoid : ∀ g ∈ pre, p ∉ g.inputs)
    (d : List ℕ) (hd : Isolated d p) :
    Isolated (pre.foldl (fun w g => w ++ [g.lineDegree w]) d) p := by
  induction pre generalizing d with
  | nil => exact hd
  | cons g gs ih =>
    apply ih (fun t ht => avoid t (List.mem_cons_of_mem _ ht))
    have zero : budget g.inputs d = 0 := by
      unfold budget
      apply List.sum_eq_zero_iff.mpr
      intro v hv
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
      have ne : i ≠ p := fun e => avoid g List.mem_cons_self (e ▸ hi)
      simpa [ne] using hd i
    have gate := gateBudget g d
    have gz : g.lineDegree d = 0 := by omega
    intro i
    by_cases small : i < d.length
    · rw [List.getD_append _ _ _ _ small]
      exact hd i
    · rw [List.getD_append_right _ _ _ _ (by omega),gz]
      cases i-d.length <;> simp [List.getD]
theorem longPrefix (pre post : List Gate) (out : ℕ) (val : Valid ⟨pre ++ post,out⟩)
    (labels : ℕ → Token) (obs : Observed pre post out labels)
    (len : 14 ≤ pre.length) (p l : Fin 7) (avoid : ∀ g ∈ pre, p.val ∉ g.inputs) :
    ¬ Both ⟨pre ++ post,out⟩ p l := by
  have upper := val.1
  change (pre ++ post).length ≤ 27 at upper
  rw [List.length_append] at upper
  have low := (suffixMinimum pre post out val labels obs).1
  have nd := tightReferences pre post out val labels obs (by omega)
  let init := (List.range 14).map fun i => if i ∈ ({p.val} : Finset ℕ) then 1 else 0
  have base : Isolated init p.val := by
    intro i
    by_cases hi : i < 14
    · have h : i < init.length := by simpa [init] using hi
      rw [List.getD_eq_getElem _ _ h]
      simp [init]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega)]
      exact Nat.zero_le _
  let d := pre.foldl (fun w (g : Gate) => w ++ [g.lineDegree w]) init
  have hd : Isolated d p.val := untouched pre p.val avoid init base
  have b := readOnceBudget post out d nd
  have bound : budget (references post out) d ≤ 1 :=
    le_trans (List.sum_le_sum (fun i _ => hd i)) (oneUse _ nd p.val 1)
  intro both
  have high := both.1
  simp only [Circuit.lineDeg,Circuit.lineDegrees,List.foldl_append] at high
  change 2 ≤ (post.foldl (fun w (g : Gate) => w ++ [g.lineDegree w]) d).getD out 0 at high
  omega
end Local4928
#print axioms Local4928.longPrefix
