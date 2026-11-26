import PEqualNP.Outside.L_meta_4127
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4127_aux
namespace LocalFano4126
def OK (d : ℕ) (v : Bool) (p : Bool × Bool) : Prop :=
  (d = 0 → v = true → p.1 = true) ∧ (d ≤ 1 → v = true → p.1 = true ∨ p.2 = true)
theorem andOK {a b x y p q} (h : OK a x p) (k : OK b y q) :
    OK (a+b) (x && y) (p.1 && q.1, (p.1 && q.2) || (p.2 && q.1)) := by
  unfold OK at *
  simp only [Bool.and_eq_true,Bool.or_eq_true] at *
  constructor
  · intro z ⟨u,v⟩; exact ⟨h.1 (by omega) u,k.1 (by omega) v⟩
  · intro z ⟨u,v⟩
    rcases h.2 (by omega) u with hp | hp
    · rcases k.2 (by omega) v with hq | hq
      · exact Or.inl ⟨hp,hq⟩
      · exact Or.inr (Or.inl ⟨hp,hq⟩)
    · by_cases small : a = 0
      · have hp0 := h.1 small u
        rcases k.2 (by omega) v with hq | hq
        · exact Or.inl ⟨hp0,hq⟩
        · exact Or.inr (Or.inl ⟨hp0,hq⟩)
      · exact Or.inr (Or.inr ⟨hp,k.1 (by omega) v⟩)
theorem orOK {a b x y p q} (h : OK a x p) (k : OK b y q) :
    OK (max a b) (x || y) (p.1 || q.1,p.2 || q.2) := by
  unfold OK at *
  simp only [Bool.or_eq_true] at *
  constructor
  · intro z v; rcases v with u | u
    · exact Or.inl (h.1 (by omega) u)
    · exact Or.inr (k.1 (by omega) u)
  · intro z v; rcases v with u | u
    · rcases h.2 (by omega) u with f | s
      · exact Or.inl (Or.inl f)
      · exact Or.inr (Or.inl s)
    · rcases k.2 (by omega) u with f | s
      · exact Or.inl (Or.inr f)
      · exact Or.inr (Or.inr s)

abbrev Shape (gs : List Gate) := ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b]
def inv (ds : List ℕ) (vs : List Bool) (ps : List (Bool × Bool)) :=
  ds.length = vs.length ∧ ds.length = ps.length ∧ ∀ i, OK (ds.getD i 0) (vs.getD i false) (ps.getD i (false,false))
theorem appendGet {α} (l : List α) (z v : α) (i : ℕ) :
    (l ++ [v]).getD i z = if i = l.length then v else l.getD i z := by
  by_cases h : i < l.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h, Nat.ne_of_lt h]
  · by_cases eq : i = l.length
    · subst i; simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega),if_neg eq]
theorem foldInv (gs : List Gate) (shape : Shape gs) (ds vs ps) (init : inv ds vs ps) :
    inv (fd (fun w (g : Gate) => g.lineDegree w) gs ds) (fd stB gs vs) (fd stL gs ps) := by
  induction gs generalizing ds vs ps with
  | nil => exact init
  | cons g gs ih =>
    apply ih (fun t ht => shape t (by simp [ht]))
    obtain ⟨lv,lp,wire⟩ := init
    obtain ⟨op,a,b,ins⟩ := shape g (by simp)
    refine ⟨by simp [lv],by simp [lp],fun i => ?_⟩
    simp only [appendGet,← lv,← lp]
    split
    · rcases op with op | op
      · simpa [Gate.lineDegree,stB,stL,stL2,op,ins,GateOp.eval] using andOK (wire a) (wire b)
      · simpa [Gate.lineDegree,stB,stL,stL2,op,ins,GateOp.eval] using orOK (wire a) (wire b)
    · exact wire i
end LocalFano4126
#print axioms LocalFano4126.foldInv
