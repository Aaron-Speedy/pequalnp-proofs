import Path2056
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.TwoPoints2056
def f0 (x : Fin 9 → Bool) := (x 0 && (x 2 || x 3 || x 4 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))
def f1 (x : Fin 9 → Bool) := (x 0 && (x 2 || x 3 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))
def f2 (x : Fin 9 → Bool) := (x 0 && (x 2 || x 8)) || (x 1 && (x 5 || x 6 || x 7 || x 8))
def f3 (x : Fin 9 → Bool) := (x 0 && (x 2 || x 8)) || (x 1 && (x 5 || x 6 || x 8))
def f4 (x : Fin 9 → Bool) := (x 0 && (x 2 || x 8)) || (x 1 && (x 5 || x 8))
def row (r : ℕ) (i : Fin 9) := r.testBit i.val
theorem lower (C : Circuit) (mono : Monotone2 C) (ev : ∀ x, C.eval (List.ofFn x) = f0 x) :
    9 ≤ C.size := by
  have hc0 : MSize 9 f0 C.size := ⟨C,mono,le_rfl,ev⟩
  obtain ⟨t0,ht0,hc1⟩ := pin f0 f1 4 (row 1) (row 17) (row 0) (row 511)
    (by decide) (by decide) (by decide) (by decide +kernel) hc0
  obtain ⟨t1,ht1,hc2⟩ := pin f1 f2 3 (row 1) (row 9) (row 0) (row 511)
    (by decide) (by decide) (by decide) (by decide +kernel) hc1
  obtain ⟨t2,ht2,hc3⟩ := pin f2 f3 7 (row 2) (row 130) (row 0) (row 511)
    (by decide) (by decide) (by decide) (by decide +kernel) hc2
  obtain ⟨t3,ht3,hc4⟩ := pin f3 f4 6 (row 2) (row 66) (row 0) (row 511)
    (by decide) (by decide) (by decide) (by decide +kernel) hc3
  let π : Fin 9 → Fin 5 := ![0,1,2,2,2,3,3,3,4]
  obtain ⟨D,hm,hs,he⟩ := relabel_size π f4 _ hc4
  have lb := PEqualNP.Outside.Path2056.lower D hm (fun x => he x)
  omega
def star : Circuit := ⟨[⟨.or,[2,3]⟩,⟨.or,[4,8]⟩,⟨.or,[9,10]⟩,⟨.and,[0,11]⟩,
    ⟨.or,[5,6]⟩,⟨.or,[7,8]⟩,⟨.or,[13,14]⟩,⟨.and,[1,15]⟩,⟨.or,[12,16]⟩],17⟩
theorem exactMinimum (s : ℕ) : MSize 9 f0 s ↔ 9 ≤ s := by
  constructor
  · rintro ⟨C,m,sz,ev⟩
    exact (lower C m ev).trans sz
  · intro hs
    exact ⟨star,by simp [star,Monotone2],hs,by decide +kernel⟩
end PEqualNP.Outside.TwoPoints2056
#print axioms PEqualNP.Outside.TwoPoints2056.exactMinimum
