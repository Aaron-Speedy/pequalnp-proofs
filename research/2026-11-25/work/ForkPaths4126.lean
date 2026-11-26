import Bypass4126
open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3793
namespace LocalFano4126
abbrev Uniform (c : Ctx) (op : Bool) := ∀ p ∈ c, p.1 = op
theorem commB : ∀ o a b, bval o a b = bval o b a := by decide
theorem shuffleB : ∀ o a b c, bval o (bval o a b) c = bval o (bval o a c) b := by decide
theorem moveAlong (c : Ctx) (op : Bool) (uni : Uniform c op) (x) (a b : Bool) :
    evalCtx c x (bval op a b) = bval op (evalCtx c x a) b := by
  induction c generalizing a with
  | nil => rfl
  | cons p c ih =>
    change evalCtx c x (bval p.1 (bval op a b) (p.2.eval x)) = bval op (evalCtx c x (bval p.1 a (p.2.eval x))) b
    rw [uni p (by simp),shuffleB]
    exact ih (fun t ht => uni t (by simp [ht])) _
abbrev RunFork (out L R : Ctx) (root : Bool) (h : Form) (x : Fin 14 → Bool) :=
  evalCtx out x (bval root (evalCtx L x (h.eval x)) (evalCtx R x (h.eval x)))
theorem uniformSide (out L R : Ctx) (root : Bool) (h : Form) (ph : Positive h)
    (po : ∀ p ∈ out, Positive p.2) (pl : ∀ p ∈ L, Positive p.2) (pr : ∀ p ∈ R, Positive p.2)
    (uni : Uniform L root) (ok : ∀ x, RunFork out L R root h x = true ↔ F x) :
    28 ≤ h.leaves + added L + added R + added out := by
  have p : ∀ t ∈ L ++ out, Positive t.2 := fun t ht => (List.mem_append.mp ht).elim (pl t) (po t)
  have big := directPathFloor (L++out) R root h ph pr p (by
    intro x
    unfold evalCtx
    rw [List.foldl_append]
    change evalCtx out x (evalCtx L x (bval root (h.eval x) (evalCtx R x (h.eval x)))) = true ↔ _
    rw [moveAlong L root uni]
    exact ok x)
  simp only [added,List.map_append,List.sum_append] at big ⊢; omega

theorem oppositeSides (out L R : Ctx) (root : Bool) (h : Form) (ph : Positive h)
    (po : ∀ p ∈ out, Positive p.2) (pl : ∀ p ∈ L, Positive p.2) (pr : ∀ p ∈ R, Positive p.2)
    (ul : Uniform L (!root)) (ur : Uniform R (!root)) (ok : ∀ x, RunFork out L R root h x = true ↔ F x) :
    28 ≤ h.leaves + added L + added R + added out := by
  cases L with
  | nil => simpa [added] using directPathFloor out R root h ph pr po ok
  | cons p L =>
    cases R with
    | nil =>
      have big := directPathFloor out (p::L) root h ph pl po (by
        intro x; have e := ok x
        change evalCtx out x (bval root (evalCtx (p::L) x (h.eval x)) (h.eval x)) = true ↔ _ at e
        rw [commB root] at e
        exact e)
      simpa [added] using big
    | cons q R =>
      let a := plug L p.2
      let b := plug R q.2
      have side (t : Bool × Form) (c : Ctx) (u : Uniform (t::c) (!root)) (x) :
          evalCtx (t::c) x (h.eval x) = bval (!root) (h.eval x) ((plug c t.2).eval x) := by
        change evalCtx c x (bval t.1 _ _) = _
        rw [u t (by simp),commB (!root) (h.eval x),moveAlong c (!root) (fun s hs => u s (by simp [hs])),commB,plugEval]
      have pa := plugPos L p.2 (pl p (by simp)) (fun t ht => pl t (by simp [ht]))
      have pb := plugPos R q.2 (pr q (by simp)) (fun t ht => pr t (by simp [ht]))
      have big := sharedForkFloor out (!root) h a b ph pa pb po (by
        intro x; have e := ok x; unfold RunFork at e
        rw [side p L ul,side q R ur] at e; simpa [a,b] using e)
      simp only [a,b,plugLeaves] at big
      change 28 ≤ h.leaves + (p.2.leaves + added L) + (q.2.leaves + added R) + added out
      have positive (f : Form) : 0 < f.leaves := by induction f <;> simp_all [DMFormula.leaves]
      have := positive h; have := positive p.2; have := positive q.2; omega
theorem uniformForkFloor (out L R : Ctx) (root opL opR : Bool) (h : Form) (ph : Positive h)
    (po : ∀ p ∈ out, Positive p.2) (pl : ∀ p ∈ L, Positive p.2) (pr : ∀ p ∈ R, Positive p.2)
    (ul : Uniform L opL) (ur : Uniform R opR) (ok : ∀ x, RunFork out L R root h x = true ↔ F x) :
    28 ≤ h.leaves + added L + added R + added out := by
  by_cases a : opL = root
  · exact uniformSide out L R root h ph po pl pr (a ▸ ul) ok
  by_cases b : opR = root
  · have sw (x) : RunFork out R L root h x = true ↔ F x := by
      unfold RunFork; rw [commB root]; exact ok x
    have big := uniformSide out R L root h ph po pr pl (b ▸ ur) sw
    omega
  have al : opL = !root := by cases opL <;> cases root <;> simp_all
  have ar : opR = !root := by cases opR <;> cases root <;> simp_all
  exact oppositeSides out L R root h ph po pl pr (al ▸ ul) (ar ▸ ur) ok
end LocalFano4126
#print axioms LocalFano4126.oppositeSides
#print axioms LocalFano4126.uniformForkFloor
