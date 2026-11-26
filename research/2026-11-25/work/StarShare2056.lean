import PairPlane2056
import FreeInput2056
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.MonoPin9738
open PEqualNP.Outside.FreeInput2056
open PEqualNP.Outside.PairPlane2056 (inc hit)
namespace PEqualNP.Outside.StarShare2056
def g (x : Fin 5 → Bool) := x 0 && (x 1 || x 2 || x 3 || x 4)
def g1 (x : Fin 5 → Bool) := x 0 && (x 1 || x 2 || x 3)
def g2 (x : Fin 5 → Bool) := x 0 && (x 1 || x 2)
def g3 (x : Fin 5 → Bool) := x 0 && x 1
def row (r : ℕ) (i : Fin 5) := r.testBit i.val

theorem starLower {s : ℕ} (hc : MSize 5 g s) : 4 ≤ s := by
  obtain ⟨t1,h1,hc1⟩ := pin g g1 4 (row 1) (row 17) (row 0) (row 31)
    (by decide) (by decide) (by decide) (by decide) hc
  obtain ⟨t2,h2,hc2⟩ := pin g1 g2 3 (row 1) (row 9) (row 0) (row 31)
    (by decide) (by decide) (by decide) (by decide) hc1
  obtain ⟨t3,h3,C,hm,sz,ev⟩ := pin g2 g3 2 (row 1) (row 5) (row 0) (row 31)
    (by decide) (by decide) (by decide) (by decide) hc2
  by_contra! fail
  have cs : C.size = 0 := by omega
  have gs : C.gates = [] := List.length_eq_zero_iff.mp cs
  have eq (x : Fin 5 → Bool) : (List.ofFn x).getD C.output false = g3 x := by
    simpa [Circuit.eval,Circuit.wires,gs] using ev x
  by_cases loc : C.output < 5
  · have ex : ∀ i : Fin 5, ∃ x : Fin 5 → Bool, x i ≠ g3 x := by decide
    obtain ⟨x,bad⟩ := ex ⟨_,loc⟩
    apply bad
    have h := eq x
    rw [List.getD_eq_getElem _ _ (by simpa using loc),List.getElem_ofFn] at h
    exact h
  · have h := eq (row 31)
    rw [List.getD_eq_default _ _ (by simp; omega)] at h
    exact (by decide : false ≠ g3 (row 31)) h

def labels (p : Fin 13) (i : Fin 5) : Fin 26 :=
  (Fin.castAdd 13 p :: (((List.finRange 13).filter (inc p)).map (Fin.natAdd 13))).getD i.val 0
def star (p : Fin 13) (x : Fin 26 → Bool) := x (Fin.castAdd 13 p) && hit p x

theorem geometry (p : Fin 13) : Function.Injective (labels p) ∧ labels p 0 = Fin.castAdd 13 p ∧
    ([1,2,3,4].map (labels p)) = (((List.finRange 13).filter (inc p)).map (Fin.natAdd 13)) := by
  revert p; decide +kernel

theorem starEq (p : Fin 13) (x : Fin 26 → Bool) : star p x = g (x ∘ labels p) := by
  obtain ⟨_,z,lines⟩ := geometry p
  have t := congrArg (fun l : List (Fin 26) => l.any x) lines
  simp only [List.any_map,List.any_filter] at t
  change _ = hit p x at t
  simp [g,star,← t,z,Function.comp_def,Bool.or_assoc]

theorem paidBound (p a b : Fin 13) (s : ℕ) (h : Free (star p) (Fin.natAdd 13 a) (Fin.natAdd 13 b) s) :
    4 ≤ s + (if inc p a && inc p b then 1 else 0) := by
  classical
  let ι := labels p
  have he : Free (fun x => g (x ∘ ι)) (Fin.natAdd 13 a) (Fin.natAdd 13 b) s := by
    rwa [← show star p = (fun x => g (x ∘ ι)) from funext (starEq p)]
  have miss : ∀ i j : Fin 13, inc i j = false → Fin.natAdd 13 j ∉ Set.range (labels i) := by
    decide +kernel
  by_cases ha : inc p a = true
  · by_cases hb : inc p b = true
    · obtain ⟨C,hm,sz,ev⟩ := pay he
      let back := Function.invFun ι
      have left : Function.LeftInverse back ι := Function.leftInverse_invFun (geometry p).1
      obtain ⟨D,dm,ds,de⟩ := relabel_size back (fun x => g (x ∘ ι)) _ ⟨C,hm,sz,ev⟩
      have sm : MSize 5 g (s+1) := ⟨D,dm,ds,fun x => (de x).trans (congrArg g (funext (fun j => congrArg x (left j))))⟩
      simpa [ha,hb] using starLower sm
    · have swap : Free (fun x => g (x ∘ ι)) (Fin.natAdd 13 b) (Fin.natAdd 13 a) s := by
        obtain ⟨D,dm,ds,de⟩ := he
        refine ⟨D,dm,ds,fun x => ?_⟩
        change D.eval (List.ofFn (Fin.snoc (α := fun _ => Bool) x (x (Fin.natAdd 13 b) || x (Fin.natAdd 13 a)))) = _
        rw [Bool.or_comm (x (Fin.natAdd 13 b))]; exact de x
      simpa [ha,hb] using starLower (outside ι (geometry p).1 g _ _ (miss p b (by simpa using hb)) swap)
  · simpa [ha] using starLower (outside ι (geometry p).1 g _ _ (miss p a (by simpa using ha)) he)

theorem sharedOrLower (a b : Fin 13) (ab : a ≠ b) (sizes : Fin 13 → ℕ)
    (admissible : ∀ p, Free (star p) (Fin.natAdd 13 a) (Fin.natAdd 13 b) (sizes p)) :
    64 ≤ 1 + 12 + ∑ p, sizes p := by
  have unique : ∀ i j : Fin 13, i ≠ j → (∑ p : Fin 13, if inc p i && inc p j then 1 else 0 : ℕ) = 1 := by decide +kernel
  have lower := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 13)))
    (fun p _ => paidBound p a b (sizes p) (admissible p))
  simp only [Finset.sum_add_distrib,unique a b ab,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at lower
  omega
end PEqualNP.Outside.StarShare2056
#print axioms PEqualNP.Outside.StarShare2056.sharedOrLower
