import Plane9738
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.Plane9738

def trail (N old : ℕ) : List Gate :=
  [⟨.or,[0,1]⟩,⟨.or,[3,9]⟩,⟨.or,[N,N+1]⟩,⟨.and,[13,N+2]⟩,⟨.or,[old,N+3]⟩]
theorem trailVal {α : Type} (d : α) (o a : α → α → α) (st : List α → Gate → List α)
    (so : ∀ W i j, st W ⟨.or,[i,j]⟩ = W ++ [o (W.getD i d) (W.getD j d)])
    (sa : ∀ W i j, st W ⟨.and,[i,j]⟩ = W ++ [a (W.getD i d) (W.getD j d)])
    (W : List α) (old : ℕ) (hw : 13 < W.length) (h : old < W.length) :
    ((trail W.length old).foldl st W).getD (W.length+4) d =
      o (W.getD old d) (a (W.getD 13 d)
        (o (o (W.getD 0 d) (W.getD 1 d)) (o (W.getD 3 d) (W.getD 9 d)))) := by
  let p := o (W.getD 0 d) (W.getD 1 d)
  let q := o (W.getD 3 d) (W.getD 9 d)
  let r := o p q
  let s := a (W.getD 13 d) r
  have one (X : List α) (v : α) : (X ++ [v]).getD X.length d = v := by simp
  have oldAt (X : List α) (v : α) (i : ℕ) (hi : i < X.length) :
      (X ++ [v]).getD i d = X.getD i d := List.getD_append _ _ _ _ hi
  have Q : st (W++[p]) ⟨.or,[3,9]⟩ = (W++[p])++[q] := by
    rw [so,oldAt _ _ _ (by omega),oldAt _ _ _ (by omega)]
  have R : st ((W++[p])++[q]) ⟨.or,[W.length,W.length+1]⟩ =
      ((W++[p])++[q])++[r] := by
    rw [so,oldAt _ _ _ (by simp),one]
    have eq : W.length+1 = (W++[p]).length := by simp
    rw [eq,one]
  have S : st (((W++[p])++[q])++[r]) ⟨.and,[13,W.length+2]⟩ =
      (((W++[p])++[q])++[r])++[s] := by
    rw [sa,oldAt _ _ _ (by simp; omega),oldAt _ _ _ (by simp; omega),oldAt _ _ _ hw]
    have eq : W.length+2 = ((W++[p])++[q]).length := by simp <;> omega
    rw [eq,one]
  simp only [trail,List.foldl_cons,List.foldl_nil]
  rw [so W 0 1]; change (st (st (st (st (W++[p]) _) _) _) _).getD _ _ = _
  rw [Q,R,S,so]
  have e3 : W.length+3 = (((W++[p])++[q])++[r]).length := by simp <;> omega
  have e4 : W.length+4 = ((((W++[p])++[q])++[r])++[s]).length := by simp <;> omega
  rw [e4,one,e3,one]
  rw [oldAt _ _ _ (by simp; omega),oldAt _ _ _ (by simp; omega),
    oldAt _ _ _ (by simp; omega),oldAt _ _ _ h]
end PEqualNP.Outside.Plane9738
