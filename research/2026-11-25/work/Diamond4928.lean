import GateChart4928
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity LocalFano4126
open PEqualNP.Outside.L_meta_5254_aux.RowStructure
namespace Local4928
def bin (join : Bool) (a b : ℕ) : Gate := ⟨if join then .or else .and,[a,b]⟩
def fork (n : ℕ) (pre : List Gate) (s : Bool) (h a b : ℕ) : Circuit :=
  let m := n + pre.length
  ⟨pre ++ [bin s h a,bin s h b,bin (!s) m (m+1)],m+2⟩
def factored (n : ℕ) (pre : List Gate) (s : Bool) (h a b : ℕ) : Circuit :=
  let m := n + pre.length
  ⟨pre ++ [bin (!s) a b,bin s h m],m+1⟩
def comb (join x y : Bool) := if join then x || y else x && y
theorem binStep (s : Bool) (w : List Bool) (a b : ℕ) : wireStep w (bin s a b) =
    w ++ [comb s (w.getD a false) (w.getD b false)] := by cases s <;> simp [wireStep,bin,comb,GateOp.eval]
theorem forkEquivalent (n : ℕ) (pre : List Gate) (s : Bool) (h a b : ℕ)
    (hh : h < n + pre.length) (ha : a < n + pre.length) (hb : b < n + pre.length)
    (x : List Bool) (hx : x.length = n) :
    (fork n pre s h a b).eval x = (factored n pre s h a b).eval x := by
  let w := pre.foldl wireStep x
  have len : w.length = n+pre.length := (lengthRun pre x).trans (by rw [hx])
  change ((pre ++ _).foldl wireStep x).getD _ false = ((pre ++ _).foldl wireStep x).getD _ false
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,binStep]
  simp only [show pre.foldl wireStep x = w from rfl, fork, factored]
  rw [← len]
  have H : h < w.length := by omega
  have B : b < w.length := by omega
  simp only [List.getD_append _ _ _ _ H,List.getD_append _ _ _ _ B]
  generalize w.getD h false = z
  generalize w.getD a false = u
  generalize w.getD b false = v
  have rule : ∀ s z u v, comb (!s) (comb s z u) (comb s z v) = comb s z (comb (!s) u v) := by decide
  simpa [List.append_assoc,List.getD_append_right, Nat.le_refl,Nat.le_add_right] using rule s z u v

theorem forkMinimum (pre : List Gate) (s : Bool) (h a b : ℕ)
    (hh : h < 14 + pre.length) (ha : a < 14 + pre.length) (hb : b < 14 + pre.length)
    (ops : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (correct : ∀ x : Fin 14 → Bool, (fork 14 pre s h a b).eval (List.ofFn x) = true ↔ F x) :
    28 ≤ (fork 14 pre s h a b).size := by
  apply Nat.succ_le_of_lt
  have eqv (x : Fin 14 → Bool) := forkEquivalent 14 pre s h a b hh ha hb (List.ofFn x) (by simp)
  have monotone : Monotone2 (factored 14 pre s h a b) := by
    intro g hg
    change g ∈ pre ++ _ at hg
    rcases List.mem_append.mp hg with hp|ht
    · obtain ⟨op,size⟩ := ops g hp
      exact ⟨by simpa using op,size⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl <;> cases s <;> simp [bin]
  have lower := PEqualNP.Outside.L_meta_7945.fano27 _ monotone (fun x => (eqv x ▸ correct x))
  simp [factored,fork,Circuit.size] at lower ⊢
  omega
end Local4928
#print axioms Local4928.forkMinimum
