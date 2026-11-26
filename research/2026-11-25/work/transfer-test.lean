import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13494_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (3937069224 * 2 ^ 32 + 3903367336) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
namespace Transfer
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

def dualGate (L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
      if g.inputs.all (fun i => decide (i < L)) then ⟨GateOp.or, g.inputs⟩ else ⟨GateOp.and, []⟩
  | GateOp.or =>
      ⟨GateOp.and, g.inputs.filter (fun i => decide (i < L))⟩
  | GateOp.not =>
      match g.inputs with
      | [] => ⟨GateOp.or, []⟩
      | i :: _ => if i < L then ⟨GateOp.not, [i]⟩ else ⟨GateOp.or, []⟩
  | op => ⟨op, g.inputs⟩

def dualGates (L : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => dualGate L g :: dualGates (L + 1) gs

theorem dualGates_length (L : ℕ) (gs : List Gate) : (dualGates L gs).length = gs.length := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih => simp [dualGates, ih]

theorem dualGate_ok (L : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (dualGate L g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (dualGate L g).inputs.length ≤ 2 := by
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  rcases hop with h | h | h
  · unfold dualGate; rw [h]; dsimp only
    split
    · exact ⟨Or.inr (Or.inl rfl), hlen⟩
    · exact ⟨Or.inl rfl, by simp⟩
  · unfold dualGate; rw [h]; dsimp only
    exact ⟨Or.inl rfl, le_trans (List.length_filter_le _ _) hlen⟩
  · unfold dualGate; rw [h]; dsimp only
    cases hi : g.inputs with
    | nil => exact ⟨Or.inr (Or.inl rfl), by simp⟩
    | cons i rest =>
      dsimp only
      split
      · exact ⟨Or.inr (Or.inr rfl), by simp⟩
      · exact ⟨Or.inr (Or.inl rfl), by simp⟩

theorem dualGates_ok (L : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ dualGates L gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing L with
  | nil => intro g hg; cases hg
  | cons g gs ih =>
    intro g' hg'
    simp only [dualGates, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact dualGate_ok L g (hgs g (by simp))
    · exact ih (L + 1) (fun x hx => hgs x (by simp [hx])) g' hg'

theorem getD_map_not (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (w.map (!·)).getD i false = !(w.getD i false) := by
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getD_eq_getElem _ _ hi]
  simp

theorem dualGate_and_all (w : List Bool) (l : List ℕ)
    (hall : l.all (fun i => decide (i < w.length)) = true) :
    (l.map fun i => (w.map (!·)).getD i false).any id = !(l.map fun i => w.getD i false).all id := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    simp only [List.map_cons, List.any_cons, List.all_cons, id_eq]
    rw [getD_map_not w i hall.1, ih hall.2]
    cases w.getD i false <;> cases (l.map fun k => w.getD k false).all id <;> rfl

theorem dualGate_and_oob (w : List Bool) (l : List ℕ)
    (hall : l.all (fun i => decide (i < w.length)) = false) :
    (l.map fun i => w.getD i false).all id = false := by
  induction l with
  | nil => simp at hall
  | cons i l ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    by_cases hlt : i < w.length
    · simp only [List.all_cons, decide_eq_true hlt, Bool.true_and] at hall
      rw [ih hall, Bool.and_false]
    · have hwi : w.getD i false = false := List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)
      rw [hwi, Bool.false_and]

theorem dualGate_or_aux (w : List Bool) (l : List ℕ) :
    ((l.filter (fun i => decide (i < w.length))).map fun i => (w.map (!·)).getD i false).all id =
      !(l.map fun i => w.getD i false).any id := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hlt : i < w.length
    · simp only [List.filter_cons, decide_eq_true hlt, ite_true, List.map_cons, List.all_cons, List.any_cons, id_eq]
      rw [getD_map_not w i hlt, ih]
      cases w.getD i false <;> cases (l.map fun k => w.getD k false).any id <;> rfl
    · have hwi : w.getD i false = false := List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)
      simp only [List.filter_cons, decide_eq_false hlt, ite_false, List.map_cons, List.any_cons, id_eq]
      rw [hwi, Bool.false_or]
      exact ih

theorem dualGate_eval (w : List Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (dualGate w.length g).op.eval ((dualGate w.length g).inputs.map fun i => (w.map (!·)).getD i false) =
      !(g.op.eval (g.inputs.map fun i => w.getD i false)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · unfold dualGate; rw [h]; dsimp only
    split
    · rename_i hall
      exact dualGate_and_all w g.inputs hall
    · rename_i hall
      have hfalse : g.inputs.all (fun i => decide (i < w.length)) = false :=
        Bool.eq_false_iff.mpr hall
      simp only [GateOp.eval, List.map_nil, List.all_nil, dualGate_and_oob w g.inputs hfalse, Bool.not_false]
  · unfold dualGate; rw [h]; dsimp only
    exact dualGate_or_aux w g.inputs
  · unfold dualGate; rw [h]; dsimp only
    cases hi : g.inputs with
    | nil => simp [GateOp.eval]
    | cons i rest =>
      dsimp only
      split
      · rename_i hlt
        simp only [GateOp.eval, List.map_cons, List.headD_cons, getD_map_not w i hlt, Bool.not_not]
      · rename_i hlt
        have hwi : w.getD i false = false := List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)
        simp only [GateOp.eval, List.map_cons, List.headD_cons]
        rw [hwi]; rfl

theorem dualGates_wires (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    ∀ w : List Bool,
      wiresFrom (dualGates w.length gs) (w.map (!·)) = (wiresFrom gs w).map (!·) := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have hg := hgs g (by simp)
    have hrest : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      fun g' hx => hgs g' (by simp [hx])
    change wiresFrom (dualGates (w.length + 1) gs)
      (w.map (!·) ++ [(dualGate w.length g).op.eval
        ((dualGate w.length g).inputs.map fun i => (w.map (!·)).getD i false)]) =
      (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).map (!·)
    rw [dualGate_eval w g hg]
    have hstep : w.map (!·) ++ [!(g.op.eval (g.inputs.map fun i => w.getD i false))] =
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).map (!·) := by simp
    rw [hstep]
    have hlen : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by simp
    rw [← hlen]
    exact ih hrest _

theorem wiresFrom_length (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]; simp; omega

theorem dual_size {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : ∃ x, f x = true) (s : ℕ)
    (h : HasCircuitSize n f s) : HasCircuitSize n (fun x => !(f (fun i => !x i))) s := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hout : C.output < n + C.gates.length := by
    by_contra hge
    obtain ⟨x0, hx0⟩ := hf
    have he := hev x0
    have hlen : (C.wires (List.ofFn x0)).length = n + C.gates.length := by
      change (wiresFrom C.gates (List.ofFn x0)).length = _
      rw [wiresFrom_length]; simp
    have hdef : C.eval (List.ofFn x0) = false :=
      List.getD_eq_default _ _ (by rw [hlen]; omega)
    rw [hdef] at he
    exact Bool.noConfusion (he.trans hx0)
  refine ⟨⟨dualGates n C.gates, C.output⟩, dualGates_ok n C.gates hfan, ?_, ?_⟩
  · simpa [Circuit.size, dualGates_length] using hsz
  · intro x
    let y : Fin n → Bool := fun i => !x i
    have hxy : List.ofFn x = (List.ofFn y).map (!·) := by
      rw [List.map_ofFn]
      congr 1; funext i; simp [y]
    have hw : (⟨dualGates n C.gates, C.output⟩ : Circuit).wires (List.ofFn x) =
        (C.wires (List.ofFn y)).map (!·) := by
      change wiresFrom (dualGates n C.gates) (List.ofFn x) = (wiresFrom C.gates (List.ofFn y)).map (!·)
      rw [hxy]
      have hdg : dualGates n C.gates = dualGates (List.ofFn y).length C.gates := by simp
      rw [hdg]
      exact dualGates_wires C.gates (fun g hg => (hfan g hg).1) (List.ofFn y)
    have hlen : (C.wires (List.ofFn y)).length = n + C.gates.length := by
      change (wiresFrom C.gates (List.ofFn y)).length = _
      rw [wiresFrom_length]; simp
    change ((⟨dualGates n C.gates, C.output⟩ : Circuit).wires (List.ofFn x)).getD C.output false = !(f y)
    rw [hw, getD_map_not _ _ (by rw [hlen]; exact hout)]
    exact congrArg (!·) (hev y)

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3941264042 * 2 ^ 32 + 3941132456)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def swapInputs : Fin 6 → Fin 6 := ![0,2,1,5,4,3]

theorem agrees : ∀ x : Fin 6 → Bool, (!(target (fun i => !x (swapInputs i)))) = fG x := by
  decide +kernel

def dualWitness : Circuit := ⟨[⟨.or, [2, 1]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [2, 1]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [11, 13]⟩], 14⟩

theorem sameSize (lower : ∀ s, HasCircuitSize 6 fG s → 9 ≤ s) : ∀ s, HasCircuitSize 6 target s → ∃ C : Circuit,
    Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = target x := by
  intro s hs
  have hd := dual_size target ⟨fun _ => true, by decide +kernel⟩ s hs
  have hr := relabel_size swapInputs _ s hd
  have hsame : (fun x : Fin 6 → Bool => !(target (fun i => !x (swapInputs i)))) = fG :=
    funext agrees
  change HasCircuitSize 6 (fun x => !(target (fun i => !x (swapInputs i)))) s at hr
  rw [hsame] at hr
  exact ⟨dualWitness, by simp [dualWitness, Monotone2],
    (show dualWitness.size ≤ 9 by decide).trans (lower s hr), by decide +kernel⟩

end Transfer
end PEqualNP.Outside.L_meta_13494_aux

