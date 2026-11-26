import TwoPoints2056
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.MonoPin9738
open PEqualNP.Outside.TwoPoints2056
namespace PEqualNP.Outside.PairPlane2056
def inc (p l : Fin 13) : Bool := [0,1,3,9].contains ((p.val+l.val)%13)
def labels (p q : Fin 13) : Fin 9 → Fin 26 :=
  let L := List.finRange 13
  let ps := L.filter fun l => inc p l && !inc q l
  let qs := L.filter fun l => inc q l && !inc p l
  let both := L.filter fun l => inc p l && inc q l
  let t := [Fin.castAdd 13 p,Fin.castAdd 13 q] ++ (ps ++ qs ++ both).map (Fin.natAdd 13)
  fun i => t.getD i.val 0
def Lp : List (Fin 9) := [2,3,4,8]
def Lq : List (Fin 9) := [5,6,7,8]
def hit (p : Fin 13) (x : Fin 26 → Bool) :=
  (List.finRange 13).any fun j => inc p j && x (Fin.natAdd 13 j)
def pair (p q : Fin 13) (x : Fin 26 → Bool) :=
  (x (Fin.castAdd 13 p) && hit p x) || (x (Fin.castAdd 13 q) && hit q x)

theorem geo (p q : Fin 13) (h : p≠q) :
    Function.Injective (labels p q) ∧
    labels p q 0 = Fin.castAdd 13 p ∧ labels p q 1 = Fin.castAdd 13 q ∧
    (Lp.map (labels p q)).Perm (((List.finRange 13).filter (inc p)).map (Fin.natAdd 13)) ∧
    (Lq.map (labels p q)).Perm (((List.finRange 13).filter (inc q)).map (Fin.natAdd 13)) := by
  revert h q p
  decide +kernel

theorem eval (p q : Fin 13) (h : p ≠ q) (x : Fin 26 → Bool) : pair p q x = f0 (x ∘ labels p q) := by
  obtain ⟨_,p0,q1,pp,qq⟩ := geo p q h
  have side (a : Fin 13) (ls : List (Fin 9))
      (perm : (ls.map (labels p q)).Perm (((List.finRange 13).filter (inc a)).map (Fin.natAdd 13))) :
      ls.any (x ∘ labels p q) = hit a x := by
    have t := perm.any_eq (f := x)
    simpa [hit,List.any_map,List.any_filter,Function.comp_def] using t
  have a := side p Lp pp
  have b := side q Lq qq
  simp [pair,f0,← a,← b,Lp,Lq,p0,q1,Bool.or_assoc]

theorem exactMinimum {p q : Fin 13} (h : p ≠ q) (s : ℕ) :
    MSize 26 (pair p q) s ↔ 9 ≤ s := by
  classical
  let ι := labels p q
  let back := Function.invFun ι
  have left : Function.LeftInverse back ι := Function.leftInverse_invFun (geo p q h).1
  constructor
  · intro hc
    obtain ⟨C,hm,sz,he⟩ := relabel_size back (pair p q) s hc
    apply (TwoPoints2056.exactMinimum s).mp
    refine ⟨C,hm,sz,fun x => (he x).trans ?_⟩
    change pair p q (x ∘ back) = f0 x
    rw [eval p q h]
    apply congrArg f0
    funext j
    exact congrArg x (left j)
  · intro hs
    obtain ⟨C,hm,sz,he⟩ := relabel_size ι f0 s ((TwoPoints2056.exactMinimum s).mpr hs)
    exact ⟨C,hm,sz,fun x => (he x).trans (eval p q h x).symm⟩
end PEqualNP.Outside.PairPlane2056
#print axioms PEqualNP.Outside.PairPlane2056.exactMinimum
