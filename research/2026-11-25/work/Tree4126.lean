import DegParts4126
import PEqualNP.Outside.L_meta_2225
import PEqualNP.Outside.L_meta_5254
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK
open PEqualNP.Outside.L_meta_4127_aux
namespace LocalFano4126
abbrev Incident (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
abbrev F (x : Fin 14 → Bool) := ∃ p l : Fin 7, Incident p l ∧
  x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
abbrev Legal (C : Circuit) := ∀ j g, C.gates[j]? = some g →
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j
abbrev Pos (C : Circuit) := ∀ p l : Fin 7, Incident p l → C.eval (List.ofFn fun i : Fin 14 =>
    decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true
abbrev Neg (C : Circuit) := ∀ x, ¬F x →
  (∀ y, (∀ i, x i = true → y i = true) → x ≠ y → F y) → C.eval (List.ofFn x) = false
theorem shapeOf {C : Circuit} (legal : Legal C) : Shape C.gates := by
  intro g hg
  obtain ⟨i,hi,e⟩ := List.getElem_of_mem hg
  obtain ⟨op,a,b,ins,_⟩ := legal i g (List.getElem?_eq_some_iff.mpr ⟨hi,e⟩)
  exact ⟨op,a,b,ins⟩
theorem exactOf (C : Circuit) (legal : Legal C) (pos : Pos C) (neg : Neg C) :
    ∀ x, C.eval (List.ofFn x) = true ↔ F x := by
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨op,a,b,ins⟩ := shapeOf legal g hg
    exact ⟨by simpa using op,by simp [ins]⟩
  intro x
  constructor
  · intro hx
    by_contra off
    obtain ⟨z,xz,m⟩ := Finite.exists_le_maximal (p := fun y => ¬ F y) off
    have hfalse := neg z m.1 (by
      intro y le ne
      by_contra f
      have zy : z ≤ y := fun i => by specialize le i; cases h : z i <;> simp_all
      exact ne (le_antisymm zy (m.2 f zy)))
    have htrue := PEqualNP.Outside.L_meta_5254_aux.eval_mono2 C mono x z (by
      intro i hi; have h := xz i; rw [hi] at h; cases e : z i with
      | false => rw [e] at h; exact False.elim ((by decide : ¬ (true ≤ false)) h)
      | true => rfl) hx
    exact Bool.noConfusion (hfalse.symm.trans htrue)
  · rintro ⟨p,l,e,hp,hl⟩
    apply PEqualNP.Outside.L_meta_5254_aux.eval_mono2 C mono _ x _ (pos p l e)
    intro i hi
    rcases (show i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l by simpa using hi) with rfl | rfl
    · exact hp
    · exact hl
def ds (s : Bool) := (List.range 14).map fun i => if mark s i then 1 else 0
theorem startOK (s : Bool) : inv (ds s) pairInput (ini (mark s) pairInput) := by
  refine ⟨by cases s <;> decide, by cases s <;> decide,fun i => ?_⟩
  by_cases hi : i < 14
  · have all : ∀ s : Bool, ∀ i : Fin 14, OK ((ds s).getD i 0) (pairInput.getD i false)
        ((ini (mark s) pairInput).getD i (false,false)) := by unfold OK; decide +kernel
    exact all s ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by simp [ds]; omega),
        List.getD_eq_default _ _ (by rw [pairInput_length]; omega),
        List.getD_eq_default _ _ (by rw [ini_len,pairInput_length]; omega)]
    simp [OK]
theorem singleAt (C : Circuit) (legal : Legal C) (s : Bool)
    (deg : HasLineDegree 14 {if s then 7 else 0} C 1)
    (on : C.eval pairInput = true) (off : C.eval (baseInput s) = false) :
    ((linearParts C (mark s) pairInput).getD C.output (false,false)).2 = true := by
  have sh := shapeOf legal
  have invs := (foldInv C.gates sh _ _ _ (startOK s)).2.2 C.output
  have initD : ds s = (List.range 14).map (fun i : ℕ => if i ∈ ({if s then 7 else 0} : Finset ℕ) then 1 else 0) := by cases s <;> decide
  rw [initD] at invs
  have yes := invs.2 deg on
  have base := congrArg (fun w : List Bool => w.getD C.output false) (fd_fst C.gates sh (ini (mark s) pairInput))
  rw [initial_base] at base
  change ((fd stL C.gates (ini (mark s) pairInput)).map Prod.fst).getD _ false = _ at base
  rw [map_fst_getD] at base
  rcases yes with h | h
  · exact False.elim (Bool.noConfusion ((h.symm.trans base).trans off))
  · exact h
theorem treeExcluded (C : Circuit) (small : C.size ≤ 27) (legal : Legal C) (pos : Pos C) (neg : Neg C)
    (fails : ∀ s : Bool, ((linearParts C (mark s) pairInput).getD C.output (false,false)).2 = false) :
    ¬ ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup := by
  intro tree
  have ex := exactOf C legal pos neg
  have on : C.eval pairInput = true := by
    apply (ex _).mpr
    exact ⟨0,0,by decide,by decide,by decide⟩
  have off (s : Bool) : C.eval (baseInput s) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    have f := (ex _).mp yes
    cases s <;> exact (by decide +kernel : ¬ F _) f
  have force (s : Bool) (d : HasLineDegree 14 {if s then 7 else 0} C 1) : False :=
    Bool.noConfusion ((singleAt C legal s d on (off s)).symm.trans (fails s))
  rcases PEqualNP.Outside.L_meta_2225 C 0 0 ⟨small,legal,ex⟩ tree (by decide) with h|h
  · exact force false h
  · exact force true h
end LocalFano4126
#print axioms LocalFano4126.treeExcluded
