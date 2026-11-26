import PEqualNP.Outside.L_meta_7533
open PEqualNP.AndCount PEqualNP.Outside.L_meta_7533
namespace Local5060
theorem missingSide {C : AndCountCircuit 42} (hc : C.Computes plane)
    (out : C.outVars = ∅) (v : V) (T : Finset V) (ind : Independent T)
    (hv : v ∉ T) (small : T.card ≤ 4) : ∃ s ∈ positions C v, Disjoint (raw C s) T := by
  obtain ⟨w,edge,avoid⟩ := avoids v T small hv
  have bigger : Independent (insert w T) := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with ea|ma <;> rcases Finset.mem_insert.mp hb with eb|mb
    · simpa only [ea,eb] using plane.loopless.irrefl w
    · exact fun e => avoid _ mb (ea ▸ e.symm)
    · exact fun e => avoid _ ma (eb ▸ e)
    · exact ind _ ma _ mb
  obtain ⟨s,hs,miss⟩ := separation hc out bigger (Finset.mem_insert_self ..) edge
  refine ⟨s,hs,Finset.disjoint_left.mpr ?_⟩
  intro a ha hT
  exact miss ⟨a,ha,Finset.mem_insert_of_mem hT⟩

theorem transversalHasEdge {C : AndCountCircuit 42} (hc : C.Computes plane)
    (out : C.outVars = ∅) (v : V) (small : (positions C v).card ≤ 4)
    (pick : Slot C → V) (uses : ∀ s ∈ positions C v, pick s ∈ raw C s ∧ pick s ≠ v) :
    ∃ s ∈ positions C v, ∃ t ∈ positions C v, plane.Adj (pick s) (pick t) := by
  classical
  by_contra! no
  let T := (positions C v).image pick
  have ind : Independent T := by
    intro a ha b hb
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hb
    exact no s hs t ht
  have hv : v ∉ T := by
    rintro h
    obtain ⟨s,hs,e⟩ := Finset.mem_image.mp h
    exact (uses s hs).2 e
  obtain ⟨s,hs,dis⟩ := missingSide hc out v T ind hv (Finset.card_image_le.trans small)
  exact Finset.disjoint_left.mp dis (uses s hs).1 (Finset.mem_image_of_mem _ hs)
end Local5060
#print axioms Local5060.transversalHasEdge
