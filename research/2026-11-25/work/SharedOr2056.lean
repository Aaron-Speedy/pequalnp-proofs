import TwoPoints2056
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.MonoPin9738
open PEqualNP.Outside.TwoPoints2056
namespace PEqualNP.Outside.SharedOr2056
def extended (x : Fin 9 → Bool) : Fin 10 → Bool := Fin.snoc (α := fun _ => Bool) x (x 4 || x 7)
def proj : Fin 10 → Fin 9 := ![0,1,2,3,4,5,6,7,8,7]

theorem crossLower (C : Circuit) (mono : Monotone2 C)
    (ev : ∀ x, C.eval (List.ofFn (extended x)) = f0 x) : 9 ≤ C.size := by
  have ess : ∃ x y : Fin 10 → Bool, (∀ j, j ≠ 4 → x j = y j) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    refine ⟨extended (row 129), extended (row 145), by decide, ?_⟩
    rw [ev,ev]; decide
  have nc : ¬ ∃ c, ∀ y : Fin 10 → Bool, C.eval (List.ofFn (Function.update y 4 false)) = c := by
    rintro ⟨c,h⟩
    have eq := (h (extended (row 0))).trans (h (extended (row 5))).symm
    rw [show Function.update (extended (row 0)) 4 false = extended (row 0) by decide,
        show Function.update (extended (row 5)) 4 false = extended (row 5) by decide,ev,ev] at eq
    exact (by decide : f0 (row 0) ≠ f0 (row 5)) eq
  obtain ⟨D,dm,dsz,de⟩ := one_drop 10 C mono 4 false ess nc
  let h := fun x : Fin 10 → Bool => D.eval (List.ofFn x)
  have hd : MSize 10 h D.size := ⟨D,dm,le_rfl,fun _ => rfl⟩
  obtain ⟨E,em,esz,ee⟩ := relabel_size proj h _ hd
  have eqIn : ∀ x : Fin 9 → Bool, Function.update (x ∘ proj) 4 false = extended (Function.update x 4 false) := by decide +kernel
  have cut : ∀ x : Fin 9 → Bool, f0 (Function.update x 4 false) = f1 x := by decide +kernel
  have hc1 : MSize 9 f1 E.size := by
    refine ⟨E,em,le_rfl,fun x => ?_⟩
    calc
      E.eval (List.ofFn x) = D.eval (List.ofFn (x ∘ proj)) := ee x
      _ = C.eval (List.ofFn (Function.update (x ∘ proj) 4 false)) := de _
      _ = f1 x := by rw [eqIn,ev,cut]
  obtain ⟨t1,ht1,hc2⟩ := pin f1 f2 3 (row 1) (row 9) (row 0) (row 511)
    (by decide) (by decide) (by decide) (by decide +kernel) hc1
  obtain ⟨t2,ht2,hc3⟩ := pin f2 f3 7 (row 2) (row 130) (row 0) (row 511)
    (by decide) (by decide) (by decide) (by decide +kernel) hc2
  obtain ⟨t3,ht3,hc4⟩ := pin f3 f4 6 (row 2) (row 66) (row 0) (row 511)
    (by decide) (by decide) (by decide) (by decide +kernel) hc3
  let π : Fin 9 → Fin 5 := ![0,1,2,2,2,3,3,3,4]
  obtain ⟨F,hm,hs,he⟩ := relabel_size π f4 _ hc4
  have lb := PEqualNP.Outside.Path2056.lower F hm (fun x => he x)
  omega
end PEqualNP.Outside.SharedOr2056
#print axioms PEqualNP.Outside.SharedOr2056.crossLower
