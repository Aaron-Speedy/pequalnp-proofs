import Mathlib
import PEqualNP.Defs
open PEqualNP.MetaComplexity
namespace SignedRect4126
variable {P N : Type} [DecidableEq P] [DecidableEq N] {n : ℕ}
def mass (W : P → N → ℤ) (A : Finset P) (B : Finset N) := ∑ i ∈ A, ∑ j ∈ B, W i j
def budget (u : Fin n → ℤ) : DMFormula n → ℤ
  | .lit i _ => u i
  | .and a b | .or a b => budget u a + budget u b
def pos : DMFormula n → Prop
  | .lit _ sign => sign = true
  | .and a b | .or a b => pos a ∧ pos b
theorem bound (W : P → N → ℤ) (X : P → Fin n → Bool) (Y : N → Fin n → Bool) (u : Fin n → ℤ)
    (cap : ∀ i A B, (∀ p ∈ A, X p i = true) → (∀ q ∈ B, Y q i = false) → mass W A B ≤ u i)
    (f : DMFormula n) (positive : pos f) (A : Finset P) (B : Finset N)
    (accept : ∀ p ∈ A, f.eval (X p) = true) (reject : ∀ q ∈ B, f.eval (Y q) = false) :
    mass W A B ≤ budget u f := by
  induction f generalizing A B with
  | lit i s =>
    change s=true at positive
    subst s
    exact cap i A B accept reject
  | or a b ha hb =>
    let L := A.filter fun p => a.eval (X p) = true
    let R := A.filter fun p => ¬ a.eval (X p) = true
    have ea (q) (hq : q ∈ B) := Bool.or_eq_false_iff.mp (reject q hq)
    have leL := ha positive.1 L B (fun p hp => (Finset.mem_filter.mp hp).2) (fun q hq => (ea q hq).1)
    have leR := hb positive.2 R B (fun p hp => (Bool.or_eq_true_iff.mp (accept p (Finset.mem_filter.mp hp).1)).resolve_left (Finset.mem_filter.mp hp).2) (fun q hq => (ea q hq).2)
    have decomp : mass W L B + mass W R B = mass W A B := Finset.sum_filter_add_sum_filter_not ..
    exact decomp ▸ add_le_add leL leR
  | and a b ha hb =>
    let L := B.filter fun q => a.eval (Y q) = false
    let R := B.filter fun q => ¬ a.eval (Y q) = false
    have ea (p) (hp : p ∈ A) := Bool.and_eq_true_iff.mp (accept p hp)
    have leL := ha positive.1 A L (fun p hp => (ea p hp).1) (fun q hq => (Finset.mem_filter.mp hq).2)
    have leR := hb positive.2 A R (fun p hp => (ea p hp).2) (fun q hq =>
      (Bool.and_eq_false_iff.mp (reject q (Finset.mem_filter.mp hq).1)).resolve_left (Finset.mem_filter.mp hq).2)
    have decomp : mass W A L + mass W A R = mass W A B := by
      unfold mass; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_filter_add_sum_filter_not ..
    exact decomp ▸ add_le_add leL leR
def occurrences (z : Fin n) : DMFormula n → ℕ
  | .lit i _ => if i=z then 1 else 0
  | .and a b | .or a b => occurrences z a + occurrences z b
theorem weigh (f : DMFormula n) (z : Fin n) (raw special : ℤ) :
    budget (fun i => if i=z then special else raw) f =
      f.leaves * raw + (occurrences z f : ℤ) * (special-raw) := by
  induction f with
  | lit i b => by_cases h : i=z <;> simp [budget,DMFormula.leaves,occurrences,h]
  | and a b ha hb | or a b ha hb =>
    simp only [budget,DMFormula.leaves,occurrences,Nat.cast_add,ha,hb]; ring
theorem exclude (W : P → N → ℤ) (X : P → Fin n → Bool) (Y : N → Fin n → Bool) (z : Fin n)
    (A : Finset P) (B : Finset N) (raw special : ℤ) (k : ℕ) (hr : 0 ≤ raw) (hs : special ≤ raw)
    (cap : ∀ i C D, (∀ p ∈ C, X p i = true) → (∀ q ∈ D, Y q i = false) → mass W C D ≤ if i=z then special else raw)
    (strict : (26-(k:ℤ))*raw + 2*special < mass W A B)
    (f : DMFormula n) (pf : pos f) (count : k+f.leaves ≤ 28) (used : 2 ≤ occurrences z f)
    (yes : ∀ p ∈ A, f.eval (X p) = true) (no : ∀ q ∈ B, f.eval (Y q) = false) : False := by
  have upper := bound W X Y _ cap f pf A B yes no
  rw [weigh] at upper
  have s : (f.leaves : ℤ) ≤ 28 - k := by omega
  have o : (2 : ℤ) ≤ occurrences z f := by omega
  have c := mul_le_mul_of_nonneg_right s hr
  have d := mul_le_mul_of_nonpos_right o (sub_nonpos.mpr hs)
  nlinarith
end SignedRect4126
#print axioms SignedRect4126.exclude
