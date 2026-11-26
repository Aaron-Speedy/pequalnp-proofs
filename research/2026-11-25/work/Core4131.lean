import PEqualNP.Defs
open PEqualNP.EdgeOwnership
namespace PEqualNP.Outside.Core4131
abbrev G : SimpleGraph (Fin 11) := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
def ordered : Finset (Fin 11 × Fin 11) := {(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(5,9),(6,7)}
def make (p : Fin 11 × Fin 11) : Sym2 (Fin 11) := s(p.1,p.2)
def core := ordered.image make
def minimum (k : ℕ) := ([11,9,7,5,3,2,1] : List ℕ).getD k 0
set_option maxRecDepth 12000 in
set_option maxHeartbeats 7500000 in
theorem coreLower (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11))
    (cutK : (G.deleteEdges ↑U).IsVertexCover ↑K) : minimum K.card ≤ (U ∩ core).card := by
  let missing (K : Finset (Fin 11)) := ordered.filter fun p => p.1 ∉ K ∧ p.2 ∉ K
  have cardinalLower : ∀ K : Finset (Fin 11), minimum K.card ≤ (missing K).card := by decide +kernel
  have orderedEdges : ∀ p ∈ ordered, p.1 < p.2 ∧ G.Adj p.1 p.2 := by decide +kernel
  have inject : Set.InjOn make ↑(missing K) := by
    intro a ha b hb equal
    have aord := (orderedEdges a (Finset.mem_filter.mp ha).1).1
    have bord := (orderedEdges b (Finset.mem_filter.mp hb).1).1
    rcases Sym2.eq_iff.mp equal with ⟨e₁,e₂⟩ | ⟨e₁,e₂⟩
    · exact Prod.ext e₁ e₂
    · exact (not_lt_of_gt (e₁ ▸ e₂ ▸ aord) bord).elim
  have subset : (missing K).image make ⊆ U ∩ core := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨listed, left, right⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_inter.mpr
    refine ⟨?_, Finset.mem_image.mpr ⟨p,listed,rfl⟩⟩
    by_contra h
    have adj : (G.deleteEdges ↑U).Adj p.1 p.2 := SimpleGraph.deleteEdges_adj.mpr ⟨(orderedEdges p listed).2, h⟩
    exact (cutK adj).elim left right
  show minimum K.card ≤ (U ∩ core).card
  have lower := cardinalLower K
  rw [← Finset.card_image_of_injOn inject] at lower
  exact lower.trans (Finset.card_le_card subset)
def otherOrdered : Finset (Fin 11 × Fin 11) := {(4,10),(5,8),(6,10),(7,9),(8,9)}
def bridges := otherOrdered.image make
def bridgeMinimum (k : ℕ) := ([5,3,1,0,0,0,0] : List ℕ).getD k 0
set_option maxRecDepth 12000 in
set_option maxHeartbeats 7500000 in
theorem bridgesLower (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11))
    (cutK : (G.deleteEdges ↑U).IsVertexCover ↑K) : bridgeMinimum K.card ≤ (U ∩ bridges).card := by
  let missing (K : Finset (Fin 11)) := otherOrdered.filter fun p => p.1 ∉ K ∧ p.2 ∉ K
  have cardinalLower : ∀ K : Finset (Fin 11), bridgeMinimum K.card ≤ (missing K).card := by decide +kernel
  have otherOrderedEdges : ∀ p ∈ otherOrdered, p.1 < p.2 ∧ G.Adj p.1 p.2 := by decide +kernel
  have inject : Set.InjOn make ↑(missing K) := by
    intro a ha b hb equal
    have aord := (otherOrderedEdges a (Finset.mem_filter.mp ha).1).1
    have bord := (otherOrderedEdges b (Finset.mem_filter.mp hb).1).1
    rcases Sym2.eq_iff.mp equal with ⟨e₁,e₂⟩ | ⟨e₁,e₂⟩
    · exact Prod.ext e₁ e₂
    · exact (not_lt_of_gt (e₁ ▸ e₂ ▸ aord) bord).elim
  have subset : (missing K).image make ⊆ U ∩ bridges := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨listed, left, right⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_inter.mpr
    refine ⟨?_, Finset.mem_image.mpr ⟨p,listed,rfl⟩⟩
    by_contra h
    have adj : (G.deleteEdges ↑U).Adj p.1 p.2 := SimpleGraph.deleteEdges_adj.mpr ⟨(otherOrderedEdges p listed).2, h⟩
    exact (cutK adj).elim left right
  show bridgeMinimum K.card ≤ (U ∩ bridges).card
  have lower := cardinalLower K
  rw [← Finset.card_image_of_injOn inject] at lower
  exact lower.trans (Finset.card_le_card subset)
end PEqualNP.Outside.Core4131
#print axioms PEqualNP.Outside.Core4131.coreLower
#print axioms PEqualNP.Outside.Core4131.bridgesLower
