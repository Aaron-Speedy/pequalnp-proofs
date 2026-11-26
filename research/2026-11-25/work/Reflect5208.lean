import MarkedCheck5208
open PEqualNP.CircuitLowerBounds
namespace Marked5208
namespace Reflection
abbrev V := Fin 26
abbrev Term := Finset V
abbrev DNF := Finset Term
def readD (x : V → Bool) (f : DNF) : Bool :=
  decide (∃ t ∈ f, ∀ u ∈ t, x u = true)
def mul (a b : DNF) : DNF := (a ×ˢ b).image (fun m => m.1 ∪ m.2)
theorem read_empty (x : V → Bool) : readD x ∅ = false := by simp [readD]
theorem read_add (x : V → Bool) (a b : DNF) :
    readD x (a ∪ b) = (readD x a || readD x b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [readD,decide_eq_true_eq,Bool.or_eq_true,Finset.mem_union]
  aesop
theorem read_mul (x : V → Bool) (a b : DNF) :
    readD x (mul a b) = (readD x a && readD x b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [readD,decide_eq_true_eq,Bool.and_eq_true,mul,Finset.mem_image,Finset.mem_product]
  constructor
  · rintro ⟨_,⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩,yes⟩
    exact ⟨⟨u,hu,fun a ha => yes a (Finset.mem_union_left _ ha)⟩,
      ⟨v,hv,fun b hb => yes b (Finset.mem_union_right _ hb)⟩⟩
  · rintro ⟨⟨u,hu,au⟩,⟨v,hv,av⟩⟩
    exact ⟨u ∪ v,⟨(u,v),⟨hu,hv⟩,rfl⟩,fun j h => (Finset.mem_union.mp h).elim (au j) (av j)⟩
def sym (w : List DNF) (g : Gate) := w ++ [match g.op,g.inputs with
  | .and,[a,b] => mul (w.getD a ∅) (w.getD b ∅)
  | .or,[a,b] => (w.getD a ∅) ∪ (w.getD b ∅)
  | _,_ => ∅]
def good (g : Gate) : Prop := ∃ a b, g.inputs = [a,b] ∧ (g.op = .and ∨ g.op = .or)
def evalStep (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
theorem runSound (gs : List Gate) (w : List DNF) (x : V → Bool) (ok : ∀ g ∈ gs, good g) :
    (gs.foldl sym w).map (readD x) = gs.foldl evalStep (w.map (readD x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun t ht => ok t (by simp [ht]))]
    apply congrArg (List.foldl evalStep · gs)
    obtain ⟨a,b,ins,h|h⟩ := ok g (by simp)
    all_goals
      simp [sym,evalStep,h,ins,GateOp.eval,read_mul,read_add]
      cases w[a]? <;> cases w[b]? <;> simp [read_empty]
def init : List DNF := List.ofFn fun i : V => ({ {i} } : DNF)
def result : DNF := (C.gates.foldl sym init).getD C.output ∅
theorem evaluates (x : V → Bool) : readD x result = C.eval (List.ofFn x) := by
  have ok (g) (hg : g ∈ C.gates) : good g := by
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hg
    obtain ⟨ops,a,b,ins,_⟩ := wellFormed i g (List.getElem?_eq_some_iff.mpr ⟨hi,eq⟩)
    exact ⟨a,b,ins,ops⟩
  have e := congrArg (fun w : List Bool => w.getD C.output false) (runSound C.gates init x ok)
  have initial : init.map (readD x) = List.ofFn x := by simp [init,List.map_ofFn,Function.comp_def,readD]
  rw [initial] at e
  change ((C.gates.foldl sym init).map (readD x)).getD C.output false = _ at e
  rw [← read_empty x,List.getD_map] at e
  exact e
end Reflection
end Marked5208
