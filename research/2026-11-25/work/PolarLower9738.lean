import Full9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.Plane9738
def leftMarks (_n : ℕ) := Finset.range 13
def leftBase (n : ℕ) := (List.range n).map (fun i => if i ∈ leftMarks n then 1 else 0)
theorem dginit_l : DegRel 25 26 emb (leftBase 25) (leftBase 26) := by
  refine ⟨by decide, by decide, ?_⟩
  intro w
  by_cases hw : w < 25
  · have fin : ∀ i : Fin 25, (leftBase 26).getD (emb i).val 0 = (leftBase 25).getD i.val 0 := by decide
    simpa [wmap,hw] using fin ⟨w,hw⟩
  · have a : (leftBase 25).length = 25 := by decide
    have b : (leftBase 26).length = 26 := by decide
    simp only [wmap,dif_neg hw]
    rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
theorem lifted_left (C : Circuit) :
    (relabel 25 26 emb C).lineDeg 26 (leftMarks 26) = C.lineDeg 25 (leftMarks 25) :=
  (degree_fold 25 26 emb C.gates _ _ dginit_l).2.2 C.output

theorem ext_left (B : Circuit) (h : B.output < 26+B.size) :
    (ext B).lineDeg 26 (leftMarks 26) = max (B.lineDeg 26 (leftMarks 26)) 1 := by
  let W := B.gates.foldl ds (leftBase 26)
  have len : W.length = 26+B.size := by simp [W,ds_len,leftBase,Circuit.size]
  have old (i : Fin 26) : W.getD i.val 0 = (leftBase 26).getD i.val 0 :=
    ds_input _ _ _ (by simp [leftBase])
  have t := trailVal 0 max (· + ·) ds
    (by intro w i j; simp [ds,Gate.lineDegree]) (by intro w i j; simp [ds,Gate.lineDegree])
    W B.output (by omega) (by omega)
  rw [len] at t
  change ((B.gates ++ trail (26+B.size) B.output).foldl ds (leftBase 26)).getD _ _ = _
  rw [List.foldl_append]
  have h0 : W.getD 0 0 = 1 := old 0
  have h1 : W.getD 1 0 = 1 := old 1
  have h3 : W.getD 3 0 = 1 := old 3
  have h9 : W.getD 9 0 = 1 := old 9
  have h13 : W.getD 13 0 = 0 := old 13
  rw [h0,h1,h3,h9,h13] at t
  exact t

def phi : Fin 26 → Fin 26 := ![13,25,24,23,22,21,20,19,18,17,16,15,14,0,12,11,10,9,8,7,6,5,4,3,2,1]
theorem phi_pt : ∀ i : Fin 13, phi (Fin.castAdd 13 i) = Fin.natAdd 13 (-i) := by decide
theorem phi_ln : ∀ i : Fin 13, phi (Fin.natAdd 13 i) = Fin.castAdd 13 (-i) := by decide
theorem polar : ∀ p l : Fin 13, I p l ↔ I (-l) (-p) := by decide
def swap (A : Circuit) := relabel 26 26 phi A
theorem swap_mono (A : Circuit) (m : Monotone2 A) : Monotone2 (swap A) := by
  intro g h
  obtain ⟨g',hg,rfl⟩ := List.mem_map.mp h
  exact ⟨(m _ hg).1,by simpa [relGate] using (m _ hg).2⟩
theorem deg_swap (A : Circuit) : (swap A).lineDeg 26 (marks 26) = A.lineDeg 26 (leftMarks 26) := by
  have hi : DegRel 26 26 phi (leftBase 26) (base 26) := by
    refine ⟨by decide,by decide,?_⟩
    intro w
    by_cases hw : w < 26
    · have h : ∀ i : Fin 26, (base 26).getD (phi i).val 0 = (leftBase 26).getD i.val 0 := by decide
      simpa [wmap,hw] using h ⟨w,hw⟩
    · have l : (leftBase 26).length = 26 := by decide
      have r : (base 26).length = 26 := by decide
      simp only [wmap,dif_neg hw]
      rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
  exact (degree_fold _ _ phi A.gates _ _ hi).2.2 A.output
theorem transEval (C : Circuit) (ok : GraphOK C) (x : Fin 26 → Bool) :
    (swap (ext (B C))).eval (List.ofFn x) = true ↔
    ∃ p l, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  have ev : (swap (ext (B C))).eval (List.ofFn x) = (ext (B C)).eval (List.ofFn (x ∘ phi)) :=
    (rel_fold _ _ phi (ext (B C)).gates _ _ (rel_init _ _ phi x)).2.2 _
  rw [ev,full_eval _ ok]
  simp only [Function.comp_apply,phi_pt,phi_ln]
  constructor
  · rintro ⟨p,l,r,hp,hl⟩
    exact ⟨-l,-p,(polar _ _).mp r,hl,hp⟩
  · rintro ⟨p,l,r,hp,hl⟩
    exact ⟨-l,-p,(polar _ _).mp r, by simpa only [neg_neg] using hl, by simpa only [neg_neg] using hp⟩
theorem sharedLeft (known : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ PEqualNP.CircuitLowerBounds.HasLineDegree 26 (Finset.Ico 13 26) C 1 ∧ (∀ x : Fin 26 → Bool, (∀ wa : Fin 13, (Finset.univ.filter (fun pa : Fin 13 => (∃ da : ℕ, da ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wa.val + da) % 13 = pa.val) ∧ x (Fin.castAdd 13 pa) = true)).card ≤ 2) → PEqualNP.MetaComplexity.circuitFun 26 C x = true → ∃ pb wb : Fin 13, (∃ db : ℕ, db ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wb.val + db) % 13 = pb.val) ∧ x (Fin.castAdd 13 pb) = true ∧ x (Fin.natAdd 13 wb) = true) ∧ (∀ pc wc : Fin 13, (∃ dc : ℕ, dc ∈ ({0, 1, 3, 9} : Finset ℕ) ∧ (wc.val + dc) % 13 = pc.val) → PEqualNP.MetaComplexity.circuitFun 26 C (fun k : Fin 26 => decide (k = Fin.castAdd 13 pc ∨ k = Fin.natAdd 13 wc)) = true))) (C : Circuit) (mono : Monotone2 C)
    (ok : GraphOK C) (deg : HasLineDegree 25 (leftMarks 25) C 1) : 59 ≤ C.size := by
  by_contra! short
  apply known
  have sz : (B C).size = C.size := by simp [B,relabel,Circuit.size]
  refine ⟨swap (ext (B C)),swap_mono _ (ext_mono _ (lift_mono C mono)),by
    have z : (swap (ext (B C))).size = (ext (B C)).size := by simp [swap,relabel,Circuit.size]
    rw [z,ext_size,sz]; omega,?_,?_,?_⟩
  · change (swap (ext (B C))).lineDeg 26 (marks 26) ≤ 1
    rw [deg_swap,ext_left _ (bound_out C ok),show (B C).lineDeg 26 (leftMarks 26) = _ from lifted_left C]
    exact max_le deg le_rfl
  · intro x _ hx
    obtain ⟨p,l,i,hp,hl⟩ := (transEval C ok x).mp hx
    exact ⟨p,l,(inc p l).mp i,hp,hl⟩
  · intro p l rel
    apply (transEval C ok _).mpr
    exact ⟨p,l,(inc p l).mpr rel,by simp,by simp⟩
end PEqualNP.Outside.Plane9738
#print axioms PEqualNP.Outside.Plane9738.sharedLeft
