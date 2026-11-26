import Normalize4928
open LocalFano4126
namespace Features4928
abbrev V := Fin 7
def linesAt (p : V) : Finset V := Finset.univ.filter fun l => decide (Incident p l)
def flags : Finset (V × V) := Finset.univ.filter fun z => decide (Incident z.1 z.2)
def credit (t : Finset V) := flags.filter fun z => z.2 ∈ t ∧ t ⊆ linesAt z.1
def Covers (tokens : Finset (Finset V)) := ∀ z ∈ flags, ∃ t ∈ tokens, z ∈ credit t

theorem capacity : ∀ t : Finset V, (credit t).card ≤ 3 := by decide +kernel
theorem saturated : ∀ t : Finset V, (credit t).card = 3 →
    (∃ l : V, t = {l}) ∨ ∃ p : V, t = linesAt p := by decide +kernel

theorem sizeBound {tokens : Finset (Finset V)} (h : Covers tokens) :
    21 ≤ ∑ t ∈ tokens, (credit t).card := by
  have sub : flags ⊆ tokens.biUnion credit := by
    intro z hz
    obtain ⟨t,ht,m⟩ := h z hz
    exact Finset.mem_biUnion.mpr ⟨t,ht,m⟩
  exact (show flags.card = 21 by decide) ▸ (Finset.card_le_card sub).trans Finset.card_biUnion_le

theorem seven {tokens : Finset (Finset V)} (h : Covers tokens) : 7 ≤ tokens.card := by
  have low := sizeBound h
  have high := Finset.sum_le_sum (s := tokens) (g := fun _ => 3) (fun t _ => capacity t)
  simp only [Finset.sum_const,smul_eq_mul] at high
  omega

theorem shape {tokens : Finset (Finset V)} (h : Covers tokens) (small : tokens.card ≤ 7)
    {t : Finset V} (mem : t ∈ tokens) : (∃ l : V, t = {l}) ∨ ∃ p, t = linesAt p := by
  apply saturated
  have low := sizeBound h
  rw [← Finset.sum_erase_add _ _ mem] at low
  have high := Finset.sum_le_sum (s := tokens.erase t) (g := fun _ => 3) (fun u _ => capacity u)
  simp only [Finset.sum_const,smul_eq_mul] at high
  have erased := Finset.card_erase_add_one mem
  have mx := capacity t
  omega

def starSet (T : Finset V) := Finset.univ.filter fun p => ∃ l ∉ T, Incident p l
theorem expansion : ∀ T : Finset V, T ≠ ∅ → T ≠ Finset.univ → 7 < T.card + (starSet T).card := by decide +kernel
theorem lineSize : ∀ p : V, (linesAt p).card = 3 := by decide +kernel
theorem uniqueStar : ∀ p q : V, linesAt q ⊆ linesAt p → q = p := by decide +kernel

theorem rigid {tokens : Finset (Finset V)} (h : Covers tokens) (small : tokens.card ≤ 7) :
    tokens = Finset.univ.image (fun l : V => ({l} : Finset V)) ∨ tokens = Finset.univ.image linesAt := by
  let T := Finset.univ.filter fun l : V => ({l} : Finset V) ∈ tokens
  let L := T.image fun l => ({l} : Finset V)
  let P := (starSet T).image linesAt
  have lsub : L ⊆ tokens := by
    intro t ht
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hl).2
  have psub : P ⊆ tokens := by
    intro t ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨l,miss,inc⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨u,hu,hh⟩ := h (p,l) (by simpa [flags] using inc)
    obtain ⟨inU,sub⟩ := (Finset.mem_filter.mp hh).2
    rcases shape h small hu with ⟨v,rfl⟩|⟨q,rfl⟩
    · obtain rfl := Finset.mem_singleton.mp inU
      exact (miss (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩)).elim
    · rwa [← uniqueStar p q sub]
  have dis : Disjoint L P := by
    apply Finset.disjoint_left.mpr
    intro t hl hp
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨p,_,e⟩ := Finset.mem_image.mp hp
    have size := lineSize p
    rw [e,Finset.card_singleton] at size
    contradiction
  have lc : L.card = T.card := Finset.card_image_of_injective _ (by intro a b e; simpa using e)
  have inject : Function.Injective linesAt := fun a b e => uniqueStar b a e.subset
  have pc : P.card = (starSet T).card := Finset.card_image_of_injective _ inject
  have count := Finset.card_le_card (Finset.union_subset lsub psub)
  rw [Finset.card_union_of_disjoint dis,lc,pc] at count
  by_cases all : T = Finset.univ
  · left
    have size : L.card = 7 := by rw [lc,all]; decide
    have eq := Finset.eq_of_subset_of_card_le lsub (by omega)
    simpa [L,all] using eq.symm
  · have empty : T = ∅ := by by_contra nonempty; have := expansion T nonempty all; omega
    have allP : starSet T = Finset.univ := by rw [empty]; decide
    have size : P.card = 7 := by rw [pc,allP]; decide
    have eq := Finset.eq_of_subset_of_card_le psub (by omega)
    exact Or.inr (by simpa [P,allP] using eq.symm)
end Features4928
#print axioms Features4928.rigid
