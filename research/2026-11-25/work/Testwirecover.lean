import GraphBase
namespace PEqualNP.Outside.L_meta_612_aux
open PEqualNP.CircuitLowerBounds
theorem freeAvoid {α : Type} {bank : Finset (Finset α)} {w : Finset α} {r : α}
    (free : FreeMeet bank w) (avoid : r ∉ w) : ∃ z ∈ bank, r ∉ z ∧ w ⊆ z := by
  classical
  obtain ⟨inputs,sub,eq⟩ := free
  have neg : ¬ ∀ z ∈ inputs, r ∈ z := fun h => avoid ((eq r).mpr h)
  push Not at neg
  obtain ⟨z,hz,miss⟩ := neg
  exact ⟨z,sub hz,miss,fun a ha => (eq a).mp ha z hz⟩

theorem wireCover {α : Type} [DecidableEq α] {bank : Finset (Finset α)}
    {w : Finset α} {k : ℕ} (h : Reach bank w k) (r : α) (avoid : r ∉ w) :
    ∃ used ⊆ bank, used.card ≤ k+1 ∧ (∀ z ∈ used, r ∉ z) ∧ w ⊆ used.biUnion id := by
  classical
  have one {B : Finset (Finset α)} (hf : FreeMeet B w) (n : ℕ) :
      ∃ used ⊆ B, used.card ≤ n+1 ∧ (∀ z ∈ used, r ∉ z) ∧ w ⊆ used.biUnion id := by
    obtain ⟨z,hz,miss,sub⟩ := freeAvoid hf avoid
    exact ⟨{z},by simpa using hz,by simp,by simpa using miss,by simpa using sub⟩
  induction k generalizing bank with
  | zero => exact one h _
  | succ k ih =>
    rcases h with stop | ⟨a,b,ha,hb,next⟩
    · exact one stop _
    obtain ⟨used,inside,bd,miss,sub⟩ := ih next
    by_cases gate : a ∪ b ∈ used
    · have missG := miss _ gate
      obtain ⟨x,hx,mx,ax⟩ := freeAvoid ha (fun ar => missG (Finset.mem_union_left _ ar))
      obtain ⟨y,hy,my,by'⟩ := freeAvoid hb (fun br => missG (Finset.mem_union_right _ br))
      let rest := used.erase (a ∪ b)
      have restSub : rest ⊆ bank := by
        intro z hz
        obtain ⟨neq,mem⟩ := Finset.mem_erase.mp hz
        exact (Finset.mem_insert.mp (inside mem)).resolve_left neq
      refine ⟨insert x (insert y rest),Finset.insert_subset hx (Finset.insert_subset hy restSub),?_,?_,?_⟩
      · have hx' := Finset.card_insert_le x (insert y rest)
        have hy' := Finset.card_insert_le y rest
        have hlen : rest.card + 1 = used.card := Finset.card_erase_add_one gate
        omega
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact mx
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact my
        exact miss _ (Finset.mem_of_mem_erase hz)
      · intro v hv
        obtain ⟨z,hz,hv⟩ := Finset.mem_biUnion.mp (sub hv)
        by_cases eq : z = a ∪ b
        · subst z
          rcases Finset.mem_union.mp hv with h | h
          · exact Finset.mem_biUnion.mpr ⟨x,by simp,ax h⟩
          · exact Finset.mem_biUnion.mpr ⟨y,by simp,by' h⟩
        · exact Finset.mem_biUnion.mpr ⟨z,by simp [rest,eq,hz],hv⟩
    · refine ⟨used,?_,by omega,miss,sub⟩
      intro z hz
      exact (Finset.mem_insert.mp (inside hz)).resolve_left (fun eq => gate (eq ▸ hz))

theorem sensitivityBound {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (sample : Option ι → Fin n → Bool) (C : Circuit) (ok : PEqualNP.MetaComplexity.Monotone2 C)
    (base : C.eval (List.ofFn (sample none)) = false)
    (hits : ∀ i, C.eval (List.ofFn (sample (some i))) = true)
    (disjoint : ∀ v, sample none v = false → ∀ a b, sample (some a) v = true →
      sample (some b) v = true → a = b) :
    Fintype.card ι ≤ orCost C.gates + 1 := by
  classical
  let target := Finset.univ.filter (fun r => C.eval (List.ofFn (sample r)))
  have run : Reach (inputBank sample) target (orCost C.gates) :=
    (searchExact _ _ _).mp (circuitSearch sample C ok)
  have avoid : none ∉ target := by simp [target,base]
  obtain ⟨used,inside,size,miss,all⟩ := wireCover run none avoid
  have limit : ∀ z ∈ used, z.card ≤ 1 := by
    intro z hz
    have mm := miss z hz
    rcases Finset.mem_insert.mp (inside hz) with rfl | inp
    · simp
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp inp
    simp at mm
    apply Finset.card_le_one.mpr
    intro a ha b hb
    cases a with
    | none =>
      have := (by simpa using ha : sample none v = true)
      simp [mm] at this
    | some a =>
      cases b with
      | none =>
        have := (by simpa using hb : sample none v = true)
        simp [mm] at this
      | some b => exact congrArg some (disjoint v mm a b (by simpa using ha) (by simpa using hb))
  have lower : Finset.univ.image (some : ι → Option ι) ⊆ used.biUnion id := by
    intro r hr
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
    apply all
    simp [target,hits]
  calc
    Fintype.card ι = (Finset.univ.image (some : ι → Option ι)).card := by
      rw [Finset.card_image_of_injective _ (Option.some_injective ι), Finset.card_univ]
    _ ≤ (used.biUnion id).card := Finset.card_le_card lower
    _ ≤ ∑ z ∈ used, z.card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ used, 1 := Finset.sum_le_sum limit
    _ ≤ orCost C.gates+1 := by simpa using size

theorem independentComplementOr {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (ok : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (s : Finset (Fin n)) (indep : ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v)
    (maximal : ∀ v ∉ s, ∃ u ∈ s, G.Adj u v) :
    sᶜ.card ≤ orCost C.gates + 1 := by
  classical
  let sample : Option {v // v ∈ sᶜ} → Fin n → Bool :=
    fun r i => match r with
      | none => decide (i ∈ s)
      | some v => decide (i ∈ s ∨ i = v.val)
  have base : C.eval (List.ofFn (sample none)) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨u,v,edge,hu,hv⟩ := (correct _).mp yes
    exact indep u (of_decide_eq_true hu) v (of_decide_eq_true hv) edge
  have hits (v : {v // v ∈ sᶜ}) : C.eval (List.ofFn (sample (some v))) = true := by
    obtain ⟨u,hu,edge⟩ := maximal v.val (Finset.mem_compl.mp v.property)
    exact (correct _).mpr ⟨u,v.val,edge,by simp [sample,hu],by simp [sample]⟩
  have sep : ∀ i, sample none i = false → ∀ a b, sample (some a) i = true →
      sample (some b) i = true → a = b := by
    intro i hi a b ha hb
    simp only [sample,decide_eq_false_iff_not] at hi
    simp [sample,hi] at ha hb
    exact Subtype.ext (ha.symm.trans hb)
  simpa using sensitivityBound sample C ok base hits sep
end PEqualNP.Outside.L_meta_612_aux
