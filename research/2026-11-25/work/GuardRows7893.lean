import PEqualNP.Defs

namespace PEqualNP.Outside.GuardRows7893

abbrev Row := BitVec 10
def subset (a b : Row) : Prop := a &&& b = a
instance (a b : Row) : Decidable (subset a b) := inferInstanceAs (Decidable (a &&& b = a))
def edges : List Row := [6,12,24,66,132,160,264,288,320,528,576,640]
def negatives : List Row := [50,104,116,138,208,276,402,548,554,770]
def minimal : List Row := edges ++ [200,772]

theorem classify : ∀ x : Row, x.getLsbD 0 = false →
    ((∀ z ∈ negatives, ¬ subset x z) ↔ ∃ m ∈ minimal, subset m x) := by
  have cert : ∀ x : Row, x.getLsbD 0 = false →
      (!(negatives.any (fun z => decide (subset x z)))) = minimal.any (fun m => decide (subset m x)) := by decide +kernel
  intro x hx
  simpa [List.any_eq_true, Bool.not_eq_true', List.any_eq_false] using
    (congrArg (fun v : Bool => v = true) (cert x hx)).to_iff

theorem incomparable : ∀ a ∈ minimal, ∀ b ∈ minimal, subset a b → a = b := by
  simp [minimal,edges,List.mem_cons,subset] <;> decide +kernel

theorem guardBound (f : Row → Bool)
    (mono : ∀ a b, subset a b → f a = true → f b = true)
    (zero : ∀ z ∈ negatives, f z = false)
    (x : Row) (even : x.getLsbD 0 = false) (active : f x = true) :
    ∃ m ∈ minimal, subset m x := by
  apply (classify x even).mp
  intro z hz sub
  have hit := mono x z sub active
  rw [zero z hz] at hit
  contradiction


def allEdges : List Row := [3,17,33] ++ edges
def allNegatives : List Row := negatives ++ [69,201,385,521,773]
def hasEdge (x : Row) : Bool := allEdges.any (fun e => decide (subset e x))

theorem covered : ∀ x : Row, hasEdge x = false → ∃ z ∈ allNegatives, subset x z := by
  have check : ∀ x : Row, hasEdge x || allNegatives.any (fun z => decide (subset x z)) = true := by decide +kernel
  intro x hx
  have h := check x
  simpa [hx,List.any_eq_true] using h

theorem separation (f : Row → Bool)
    (mono : ∀ a b, subset a b → f a = true → f b = true)
    (pos : ∀ e ∈ allEdges, f e = true) (neg : ∀ z ∈ allNegatives, f z = false) :
    ∀ x, f x = hasEdge x := by
  intro x
  cases h : hasEdge x with
  | false =>
    obtain ⟨z,hz,hs⟩ := covered x h
    cases hf : f x with
    | false => rfl
    | true =>
      have contradicts := mono x z hs hf
      rw [neg z hz] at contradicts
      contradiction
  | true =>
    obtain ⟨e,he,sub⟩ := List.any_eq_true.mp h
    exact mono e x (of_decide_eq_true sub) (pos e he)

end PEqualNP.Outside.GuardRows7893
#print axioms PEqualNP.Outside.GuardRows7893.guardBound
