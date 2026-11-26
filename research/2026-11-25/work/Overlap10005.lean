import PEqualNP.Outside.L_meta_10004
namespace PEqualNP.Outside.Matrix10005
open PEqualNP.Outside.L_meta_10004_aux
open scoped BigOperators

private theorem reflected_energy (K : Submodule ℝ E) (i : V) :
    ∑ j : V, ((K.reflection (q i)) j)^2 = 121 := by
  have h := norm_q i
  have hr : ‖K.reflection (q i)‖ = 11 := (K.reflection.norm_map _).trans h
  rw [EuclideanSpace.norm_eq] at hr
  simp only [Real.norm_eq_abs, sq_abs] at hr
  have pos : 0 ≤ ∑ j : V, ((K.reflection (q i)) j)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [Real.sq_sqrt pos]

def mult (R : Fin 15 → Box) (i j : V) : ℕ :=
  (Finset.univ.filter (fun t => i ∈ (R t).1 ∧ j ∈ (R t).2)).card

private theorem count_charge (R : Fin 15 → Box) (K : Submodule ℝ E) (i j : V) :
    ∑ t, cellCharge K (R t) i j = (mult R i j : ℝ) * w K i j := by
  classical
  simp [cellCharge,mult,← Finset.sum_filter]

private theorem row_energy (K : Submodule ℝ E) (m : V → ℝ) (i : V) :
    ∑ j : V, (8*m j*(11-w K i j)-16*(m j)^2) ≤ 121 := by
  rw [← reflected_energy K i]
  apply Finset.sum_le_sum
  intro j _
  unfold w
  nlinarith [sq_nonneg ((K.reflection (q i)) j - 4*m j)]

private theorem full_energy (K : Submodule ℝ E) (m : V → V → ℝ) :
    ∑ j : V, ∑ i : V, (8*m i j*(11-w K i j)-16*(m i j)^2) ≤ 3751 := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i : V, (121:ℝ) := Finset.sum_le_sum (fun i _ => row_energy K (m i) i)
    _ = _ := by norm_num



private theorem move_outer (f : V → V → Fin 15 → ℝ) :
    ∑ j, ∑ i, ∑ t, f j i t = ∑ t, ∑ j, ∑ i, f j i t := by
  calc
    _ = ∑ j, ∑ t, ∑ i, f j i t :=
      Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

private theorem sum_mult (R : Fin 15 → Box) :
    ∑ j : V, ∑ i : V, (mult R i j : ℝ) =
      ∑ t, ((R t).1.card : ℝ) * (R t).2.card := by
  classical
  have one (i j : V) : (mult R i j : ℝ) =
      ∑ t : Fin 15, if i ∈ (R t).1 ∧ j ∈ (R t).2 then (1:ℝ) else 0 := by
    simp [mult]
  simp_rw [one]
  rw [move_outer]
  apply Finset.sum_congr rfl
  intro t _
  have col (j : V) : (∑ i : V, if i ∈ (R t).1 ∧ j ∈ (R t).2 then (1:ℝ) else 0) =
      if j ∈ (R t).2 then ((R t).1.card : ℝ) else 0 := by
    by_cases h : j ∈ (R t).2 <;> simp [h]
  simp [col,mul_comm]

private theorem sum_charges (R : Fin 15 → Box) (good : ∀ t, plain (R t))
    (K : Submodule ℝ E) (mem : ∀ t, rowVector (R t) ∈ K) :
    ∑ j : V, ∑ i : V, (mult R i j : ℝ) * w K i j =
      10 * ∑ t, ((R t).1.card : ℝ) * (R t).2.card := by
  simp_rw [← count_charge]
  rw [move_outer]
  simp only [cc_total, fun t => charge_eq K (R t) (mem t) (good t),
    mul_assoc, Finset.mul_sum]

def base (i j : V) : ℝ := if i ∈ zeros j then 1 else 0

private theorem base_size : ∑ j : V, ∑ i : V, base i j = 775 := by
  norm_num [base,count_table]

private theorem base_weight (K : Submodule ℝ E) :
    ∑ j : V, ∑ i : V, base i j * w K i j = 9300-50*(Module.finrank ℝ K : ℝ) := by
  simpa [base,ite_mul,← Finset.sum_filter] using w_total K



theorem someTriple (R : Fin 15 → Box) (good : ∀ t, plain (R t))
    (cover : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    ∃ i j, 3 ≤ mult R i j := by
  classical
  by_contra! small
  let K := Submodule.span ℝ (Set.range (fun t => rowVector (R t)))
  have mem (t : Fin 15) : rowVector (R t) ∈ K :=
    Submodule.subset_span (Set.mem_range_self t)
  have dim : Module.finrank ℝ K ≤ 15 := by
    simpa [K, Set.finrank] using (finrank_range_le_card (R:=ℝ) (fun t => rowVector (R t)))
  have dimR : (Module.finrank ℝ K : ℝ) ≤ 15 := by exact_mod_cast dim
  let m (i j : V) : ℝ := (mult R i j : ℝ) - base i j
  have mm (i j : V) : (m i j)^2 = m i j := by
    by_cases z : i ∈ zeros j
    · obtain ⟨t, ht⟩ := cover i j (Finset.mem_filter.mp z).2
      have pos : 0 < mult R i j :=
        Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩⟩
      have bound := small i j
      have cases : mult R i j = 1 ∨ mult R i j = 2 := by omega
      rcases cases with h|h <;> norm_num [m,base,z,h]
    · have empty : mult R i j = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t h
        obtain ⟨hi,hj⟩ := (Finset.mem_filter.mp h).2
        exact z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,good t i hi j hj⟩)
      simp [m,base,z,empty]
  have rearr (i j : V) :
      8*m i j*(11-w K i j)-16*(m i j)^2 =
      72*(mult R i j : ℝ)-72*base i j-8*((mult R i j : ℝ)*w K i j)+8*(base i j*w K i j) := by
    rw [mm]; dsimp [m]; ring
  have H := full_energy K m
  simp_rw [rearr] at H
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    sum_mult,base_size,sum_charges R good K mem,base_weight] at H
  have upper : (∑ t, ((R t).1.card : ℝ) * (R t).2.card) ≤ 900 := by
    calc
      _ ≤ ∑ _t : Fin 15, (60:ℝ) := Finset.sum_le_sum (fun t _ => by
        exact_mod_cast Area.matrix_area_le_60 _ _ (good t))
      _ = _ := by norm_num
  linarith

theorem manyLargeOrFourfold (R : Fin 15 → Box) (good : ∀ t, plain (R t))
    (cover : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    12 ≤ (Finset.univ.filter (fun t => 56 < (R t).1.card * (R t).2.card)).card ∨
      ∃ i j, 4 ≤ mult R i j := by
  classical
  by_contra! bad
  obtain ⟨few,small⟩ := bad
  let K := Submodule.span ℝ (Set.range (fun t => rowVector (R t)))
  have mem (t : Fin 15) : rowVector (R t) ∈ K :=
    Submodule.subset_span (Set.mem_range_self t)
  have dim : Module.finrank ℝ K ≤ 15 := by
    simpa [K, Set.finrank] using (finrank_range_le_card (R:=ℝ) (fun t => rowVector (R t)))
  have dimR : (Module.finrank ℝ K : ℝ) ≤ 15 := by exact_mod_cast dim
  let m (i j : V) : ℝ := (mult R i j : ℝ) - base i j
  have mm (i j : V) : (m i j)^2 ≤ 2*m i j := by
    by_cases z : i ∈ zeros j
    · obtain ⟨t, ht⟩ := cover i j (Finset.mem_filter.mp z).2
      have pos : 0 < mult R i j :=
        Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩⟩
      have bound := small i j
      have cases : mult R i j = 1 ∨ mult R i j = 2 ∨ mult R i j = 3 := by omega
      rcases cases with h|h|h <;> norm_num [m,base,z,h]
    · have empty : mult R i j = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t h
        obtain ⟨hi,hj⟩ := (Finset.mem_filter.mp h).2
        exact z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,good t i hi j hj⟩)
      simp [m,base,z,empty]
  have rearr (i j : V) :
      56*(mult R i j : ℝ)-56*base i j-8*((mult R i j : ℝ)*w K i j)+8*(base i j*w K i j) ≤
      8*m i j*(11-w K i j)-16*(m i j)^2 := by
    calc
      _ = 8*m i j*(11-w K i j)-32*m i j := by dsimp [m]; ring
      _ ≤ _ := by linarith only [mm i j]
  have H := (Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun i _ => rearr i j))).trans (full_energy K m)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    sum_mult,base_size,sum_charges R good K mem,base_weight] at H
  let big := Finset.univ.filter (fun t => 56 < (R t).1.card * (R t).2.card)
  have card : big.card ≤ 11 := by change big.card < 12 at few; omega
  have each (t : Fin 15) : (R t).1.card * (R t).2.card ≤ 56 + (if t ∈ big then 4 else 0) := by
    by_cases h : t ∈ big
    · simpa [h] using Area.matrix_area_le_60 _ _ (good t)
    · have low : ¬ 56 < (R t).1.card * (R t).2.card := by simpa [big] using h
      simp [h]; omega
  have tot := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => each t)
  have count : (∑ t : Fin 15, if t ∈ big then 4 else 0) = big.card * 4 := by simp
  simp only [Finset.sum_add_distrib,count,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at tot
  have ub : (∑ t, (R t).1.card * (R t).2.card) ≤ 884 := by omega
  have ubR : (∑ t, ((R t).1.card : ℝ) * (R t).2.card) ≤ 884 := by exact_mod_cast ub
  linarith

theorem excessPairs (R : Fin 15 → Box) (good : ∀ t, plain (R t))
    (cover : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    52 ≤ ∑ j : V, ∑ i : V, (mult R i j - 1).choose 2 := by
  classical
  let K := Submodule.span ℝ (Set.range (fun t => rowVector (R t)))
  have mem (t : Fin 15) : rowVector (R t) ∈ K :=
    Submodule.subset_span (Set.mem_range_self t)
  have dim : Module.finrank ℝ K ≤ 15 := by
    simpa [K, Set.finrank] using (finrank_range_le_card (R:=ℝ) (fun t => rowVector (R t)))
  have dimR : (Module.finrank ℝ K : ℝ) ≤ 15 := by exact_mod_cast dim
  let m (i j : V) : ℝ := (mult R i j : ℝ) - base i j
  let p (i j : V) : ℕ := (mult R i j - 1).choose 2
  have choose_aux (n : ℕ) : 2*n.choose 2 + n = n*n := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      nlinarith
  have mm (i j : V) : (m i j)^2 = m i j + 2*(p i j : ℝ) := by
    by_cases z : i ∈ zeros j
    · obtain ⟨t, ht⟩ := cover i j (Finset.mem_filter.mp z).2
      have pos : 0 < mult R i j :=
        Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩⟩
      have cast : ((mult R i j - 1 : ℕ) : ℝ) = (mult R i j : ℝ) - 1 :=
        Nat.cast_sub (by omega) |>.trans (by norm_num)
      have h := choose_aux (mult R i j - 1)
      have hR : 2*(p i j : ℝ) + ((mult R i j - 1 : ℕ) : ℝ) =
          ((mult R i j - 1 : ℕ) : ℝ)*((mult R i j - 1 : ℕ) : ℝ) := by exact_mod_cast h
      rw [cast] at hR
      simp only [m,base,if_pos z]
      nlinarith only [hR]
    · have empty : mult R i j = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t h
        obtain ⟨hi,hj⟩ := (Finset.mem_filter.mp h).2
        exact z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,good t i hi j hj⟩)
      norm_num [m,p,base,z,empty]
  have rearr (i j : V) :
      8*m i j*(11-w K i j)-16*(m i j)^2 =
      72*(mult R i j : ℝ)-72*base i j-8*((mult R i j : ℝ)*w K i j)+8*(base i j*w K i j)-32*(p i j : ℝ) := by
    rw [mm]; dsimp [m]; ring
  have H := full_energy K m
  simp_rw [rearr] at H
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    sum_mult,base_size,sum_charges R good K mem,base_weight] at H
  have upper : (∑ t, ((R t).1.card : ℝ) * (R t).2.card) ≤ 900 := by
    calc
      _ ≤ ∑ _t : Fin 15, (60:ℝ) := Finset.sum_le_sum (fun t _ => by
        exact_mod_cast Area.matrix_area_le_60 _ _ (good t))
      _ = _ := by norm_num
  have hR : (51:ℝ) < ∑ j : V, ∑ i : V, (p i j : ℝ) := by linarith
  have hn : 51 < ∑ j : V, ∑ i : V, p i j := by exact_mod_cast hR
  exact hn

end PEqualNP.Outside.Matrix10005
#print axioms PEqualNP.Outside.Matrix10005.someTriple

#print axioms PEqualNP.Outside.Matrix10005.manyLargeOrFourfold

#print axioms PEqualNP.Outside.Matrix10005.excessPairs
