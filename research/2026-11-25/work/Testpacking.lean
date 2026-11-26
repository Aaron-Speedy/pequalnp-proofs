import GraphBase
namespace PEqualNP.Outside.L_meta_612_aux
open PEqualNP.CircuitLowerBounds
theorem separatedSubset {α : Type} [Fintype α] [DecidableEq α]
    {bank : Finset (Finset α)} {w rows : Finset α} {k : ℕ} (h : Reach bank w k)
    (inside : rows ⊆ w)
    (sep : ∀ a ∈ rows, ∀ b ∈ rows, a ≠ b → ¬ hull bank {a,b} ⊆ w) :
    rows.card ≤ 2 ^ k := by
  classical
  obtain ⟨ts,bd,free,eq⟩ := coverByMeets h
  have sub : ∀ z ∈ ts, z ⊆ w := fun z hz r hr =>
    eq ▸ Finset.mem_biUnion.mpr ⟨z,hz,hr⟩
  have limit : ∀ z ∈ ts, (z ∩ rows).card ≤ 1 := by
    intro z hz
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haz,har⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbz,hbr⟩ := Finset.mem_inter.mp hb
    by_contra ne
    apply sep a har b hbr ne
    exact (leastHull (free z hz) (Finset.insert_subset haz (Finset.singleton_subset_iff.mpr hbz))).trans (sub z hz)
  have all : rows ⊆ ts.biUnion (fun z => z ∩ rows) := by
    intro r hr
    have hw := inside hr
    rw [← eq] at hw
    obtain ⟨z,hz,hzr⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_inter.mpr ⟨hzr,hr⟩⟩
  calc
    rows.card ≤ _ := Finset.card_le_card all
    _ ≤ ∑ z ∈ ts, (z ∩ rows).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ ts, 1 := Finset.sum_le_sum limit
    _ ≤ 2 ^ k := by simpa using bd

theorem falseFamily {n : ℕ} (C : Circuit) (ok : PEqualNP.MetaComplexity.Monotone2 C)
    (rows : Finset (Fin n → Bool))
    (negative : ∀ x ∈ rows, C.eval (List.ofFn x) = false)
    (separated : ∀ a ∈ rows, ∀ b ∈ rows, a ≠ b →
      C.eval (List.ofFn (fun i => a i || b i)) = true) :
    rows.card ≤ 2 ^ andCost C.gates := by
  classical
  let w := Finset.univ.filter (fun x : Fin n → Bool => !C.eval (List.ofFn x))
  have run := circuitAndSearch (fun (x : Fin n → Bool) i => x i) C ok
  apply separatedSubset ((searchExact _ _ _).mp run)
  · intro x hx
    simp [negative x hx]
  · intro a ha b hb ne bad
    let v : Fin n → Bool := fun i => a i || b i
    have vgood : v ∈ hull (inputBank (fun (x : Fin n → Bool) i => !(x i))) {a,b} := by
      apply memHull.mpr
      intro z hz sub
      rcases Finset.mem_insert.mp hz with rfl | inp
      · have := sub (Finset.mem_insert_self _ _)
        simp at this
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp inp
      have aa := sub (Finset.mem_insert_self _ _)
      have bb := sub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      simp_all [v]
    have contra := bad vgood
    simp [v,separated a ha b hb ne] at contra

theorem independentFamily {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (ok : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (family : Finset (Finset (Fin n)))
    (independent : ∀ s ∈ family, ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v)
    (cross : ∀ s ∈ family, ∀ t ∈ family, s ≠ t → ∃ u ∈ s, ∃ v ∈ t, G.Adj u v) :
    family.card ≤ 2 ^ andCost C.gates := by
  classical
  let bits (s : Finset (Fin n)) (i : Fin n) := decide (i ∈ s)
  have inj : Function.Injective bits := by
    intro s t e
    ext i
    have := congrFun e i
    simpa [bits] using this
  rw [← Finset.card_image_of_injective family inj]
  apply falseFamily C ok
  · intro x hx
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hx
    apply Bool.eq_false_iff.mpr
    rintro yes
    obtain ⟨u,v,edge,hu,hv⟩ := (correct _).mp yes
    exact independent s hs u (of_decide_eq_true hu) v (of_decide_eq_true hv) edge
  · intro x hx y hy ne
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u,hu,v,hv,edge⟩ := cross s hs t ht (fun e => ne (congrArg bits e))
    exact (correct _).mpr ⟨u,v,edge,by simp [bits,hu],by simp [bits,hv]⟩

def IndependentRows {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v

noncomputable def maximalIndependentFamily {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (fun s => IndependentRows G s ∧
    ∀ t, IndependentRows G t → s ⊆ t → t = s)

theorem maximalIndependentCount {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (ok : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    (maximalIndependentFamily G).card ≤ 2 ^ andCost C.gates := by
  classical
  have member {s} (hs : s ∈ maximalIndependentFamily G) :
      IndependentRows G s ∧ ∀ t, IndependentRows G t → s ⊆ t → t = s := by
    simpa [maximalIndependentFamily] using hs
  apply independentFamily G C ok correct _ (fun s hs => (member hs).1)
  intro s hs t ht diff
  by_contra! no
  have un : IndependentRows G (s ∪ t) := by
    intro u hu v hv edge
    rcases Finset.mem_union.mp hu with su | tu <;> rcases Finset.mem_union.mp hv with sv | tv
    · exact (member hs).1 u su v sv edge
    · exact no u su v tv edge
    · exact no v sv u tu edge.symm
    · exact (member ht).1 u tu v tv edge
  exact diff (((member hs).2 _ un Finset.subset_union_left).symm.trans
    ((member ht).2 _ un Finset.subset_union_right))
end PEqualNP.Outside.L_meta_612_aux
