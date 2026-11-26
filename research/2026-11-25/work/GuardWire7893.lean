import PEqualNP.Defs
namespace PEqualNP.Outside.GuardWire7893
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
def listLe (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (w1 w2 : List Bool) (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    op.eval (l.map fun i => w1.getD i false) = true →
      op.eval (l.map fun i => w2.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hle i (h (w1.getD i false) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h1⟩
    exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hle i h1⟩

theorem wires_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w1 w2 : List Bool) (hle : listLe w1 w2) :
    listLe (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1)
           (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2) := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hm g List.mem_cons_self
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp [hle.1], fun i hi => ?_⟩
    simp only [List.getD_eq_getElem?_getD] at hi ⊢
    by_cases hlt : i < w1.length
    · have hlt2 : i < w2.length := by rw [← hle.1]; exact hlt
      rw [List.getElem?_append_left hlt] at hi
      rw [List.getElem?_append_left hlt2]
      exact hle.2 i (by simpa [List.getD_eq_getElem?_getD] using hi)
    · by_cases heq : i = w1.length
      · subst heq
        rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at hi
        rw [hle.1, List.getElem?_append_right (le_refl _), Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.getD_some] at hi ⊢
        exact gate_mono g.op hop g.inputs w1 w2 hle.2 hi
      · rw [List.getElem?_eq_none (by simp; omega)] at hi
        simp at hi


def row (r : BitVec 10) : Fin 10 → Bool := fun i => r.getLsbD i.val
def wire (C : Circuit) (w : ℕ) (r : BitVec 10) :=
  (C.wires (List.ofFn (Function.update (row r) 0 false))).getD w false

theorem wireMonotone (C : Circuit) (w : ℕ) (ao : IsAO2 10 C)
    (a b : BitVec 10) (sub : a &&& b = a) : wire C w a = true → wire C w b = true := by
  apply (wires_mono C.gates (fun g hg => ⟨by simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,
    le_of_eq (ao.2.2 g hg)⟩) _ _ ?_).2 w
  refine ⟨by simp,?_⟩
  intro i hi
  by_cases h : i < 10
  · have ix (r : BitVec 10) : i < (List.ofFn (Function.update (row r) 0 false)).length := by simpa using h
    rw [List.getD_eq_getElem _ _ (ix a),List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (ix b),List.getElem_ofFn]
    by_cases z : (⟨i,h⟩ : Fin 10) = 0
    · simp [z] at hi
    · simp only [Function.update_of_ne z,row] at hi ⊢
      have eq := congrArg (fun r : BitVec 10 => r.getLsbD i) sub
      simpa [BitVec.getLsbD_and,hi] using eq
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction
end PEqualNP.Outside.GuardWire7893
#print axioms PEqualNP.Outside.GuardWire7893.wireMonotone
