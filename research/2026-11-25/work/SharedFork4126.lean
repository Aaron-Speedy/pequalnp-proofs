import Tree4126
import PEqualNP.Outside.L_meta_3793
open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3793 PEqualNP.Outside.L_meta_3793.Fano
namespace LocalFano4126
abbrev Form := DMFormula 14
theorem formulaFloor (f : Form) (pos : Positive f) (good : ∀ x, f.eval x = true ↔ F x) :
    28 ≤ f.leaves := by
  classical
  have sem : ∀ x, f.eval x = true ↔ ∃ u v, fanoGraph.Adj u v ∧ x u = true ∧ x v = true := by
    intro x; rw [good]
    constructor
    · rintro ⟨p,l,e,hp,hl⟩
      exact ⟨point p,line l,(fanoAdj_iff _ _).mpr ⟨p,l,e,Or.inl ⟨rfl,rfl⟩⟩,hp,hl⟩
    · rintro ⟨u,v,uv,hu,hv⟩
      obtain ⟨p,l,e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (fanoAdj_iff _ _).mp uv
      · exact ⟨p,l,e,hu,hv⟩
      · exact ⟨p,l,e,hv,hu⟩
  obtain ⟨win,lose,edge,slots⟩ := formula_rank fanoGraph f triangleFree_fano noFour_fano pos sem
  have seven := vertexCover_card_ge _ (cover_of_winners fanoGraph lose win edge)
  have size : Fintype.card (↥fanoGraph.edgeFinset) = 21 := by rw [Fintype.card_coe,edgeCard_fano]
  by_contra! h
  have short : (leafLabels f).length ≤ Fintype.card (↥fanoGraph.edgeFinset) + 7 := by rw [leafLabels_length,size]; omega
  have e := (tight_slots lose win (leafLabels f) 7 seven short slots).2.1
  rw [leafLabels_length,size] at e; omega

def branch (disj : Bool) (a b : Form) := if disj then DMFormula.or a b else DMFormula.and a b
def bval (disj a b : Bool) := bif disj then a || b else a && b
theorem branchEval (op) (a b : Form) (x) :
    (branch op a b).eval x = bval op (a.eval x) (b.eval x) := by cases op <;> rfl
theorem branchPos (op) {a b : Form} (p : Positive a) (q : Positive b) : Positive (branch op a b) := by
  cases op <;> exact ⟨p,q⟩
theorem branchLeaves (op) (a b : Form) : (branch op a b).leaves = a.leaves + b.leaves := by cases op <;> rfl

/-- Each entry adds a sibling formula and one AND or OR on the path to the output. -/
abbrev Ctx := List (Bool × Form)
def plug (c : Ctx) (f : Form) := c.foldl (fun g p => branch p.1 g p.2) f
def evalCtx (c : Ctx) (x : Fin 14 → Bool) (v : Bool) := c.foldl (fun w p => bval p.1 w (p.2.eval x)) v
def added (c : Ctx) := (c.map (fun p => p.2.leaves)).sum
theorem plugEval (c : Ctx) (f : Form) (x) : (plug c f).eval x = evalCtx c x (f.eval x) := by
  induction c generalizing f with
  | nil => rfl
  | cons p c ih => exact (ih (branch p.1 f p.2)).trans (by rw [branchEval]; rfl)
theorem plugLeaves (c : Ctx) (f : Form) : (plug c f).leaves = f.leaves + added c := by
  induction c generalizing f with
  | nil => simp [plug,added]
  | cons p c ih =>
    change (plug c (branch p.1 f p.2)).leaves = _
    rw [ih,branchLeaves]; simp [added,Nat.add_assoc]
theorem plugPos (c : Ctx) (f : Form) (pf : Positive f) (pc : ∀ p ∈ c, Positive p.2) :
    Positive (plug c f) := by
  induction c generalizing f with
  | nil => exact pf
  | cons p c ih => exact ih _ (branchPos _ pf (pc _ (by simp))) (fun t ht => pc t (by simp [ht]))

/-- The common formula h is paid for once and read by two gates. The third gate combines them. -/
theorem sharedForkFloor (c : Ctx) (op : Bool) (h a b : Form)
    (ph : Positive h) (pa : Positive a) (pb : Positive b) (pc : ∀ p ∈ c, Positive p.2)
    (correct : ∀ x, evalCtx c x (bval (!op) (bval op (h.eval x) (a.eval x))
      (bval op (h.eval x) (b.eval x))) = true ↔ F x) :
    28 ≤ (h.leaves-1) + (a.leaves-1) + (b.leaves-1) + 3 + added c := by
  let g := branch op h (branch (!op) a b)
  have hg : Positive g := branchPos _ ph (branchPos _ pa pb)
  have law : ∀ op H A B : Bool, bval op H (bval (!op) A B) = bval (!op) (bval op H A) (bval op H B) := by decide
  have exactG (x) : (plug c g).eval x = true ↔ F x := by
    rw [plugEval]; simp only [g,branchEval,law op (h.eval x) (a.eval x) (b.eval x)]
    exact correct x
  have big := formulaFloor _ (plugPos c g hg pc) exactG
  rw [plugLeaves] at big
  simp only [g,branchLeaves] at big
  have nonempty (t : Form) : 0 < t.leaves := by
    induction t <;> simp_all [DMFormula.leaves] <;> omega
  have := nonempty h; have := nonempty a; have := nonempty b
  omega
end LocalFano4126
#print axioms LocalFano4126.sharedForkFloor
