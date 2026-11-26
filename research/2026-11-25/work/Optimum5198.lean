import Upper5198
import Linear5198
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.Outside.Join5198
namespace PEqualNP.Outside.Optimum5198
def nested (C : Circuit) (j : ℕ) := (gateAt C j).op = GateOp.and ∧
    ∃ i ∈ (gateAt C j).inputs, 26 ≤ i ∧ (gateAt C (i-26)).op = GateOp.and
def accepted (C : Circuit) (a b : ℕ) :=
    Monotone2 C ∧ ReadsBack 26 C ∧ a < 26+C.size ∧ b < 26+C.size ∧
    (∀ p l : Fin 13, p ∈ singerLines3 l → W C a {p} {l} = true ∨ W C b {p} {l} = true) ∧
    (∀ Q, IsQuadrangle singerLines3 Q → W C a Q (missLines singerLines3 Q) = false ∧ W C b Q (missLines singerLines3 Q) = false) ∧
    (∃ p l : Fin 13, p ∈ singerLines3 l ∧ W C a {p} {l} = true ∧ W C b {p} {l} = false) ∧
    (∃ p l : Fin 13, p ∈ singerLines3 l ∧ W C b {p} {l} = true ∧ W C a {p} {l} = false) ∧
    (∀ j ∈ Finset.range C.size, ∀ k ∈ Finset.range C.size, nested C j → nested C k → j=k)

theorem witness : accepted Upper5198.C 29 88 := by
  obtain ⟨hm,hr,sz,flat⟩ := Upper5198.structure_ok
  have ⟨one,two⟩ := Upper5198.exclusive
  refine ⟨hm,hr,by omega,by omega,Upper5198.positive,fun Q _ => Upper5198.negative Q,
    ⟨0,0,by decide,one⟩,⟨1,1,by decide,two.2,two.1⟩,?_⟩
  intro j hj k hk h _
  obtain ⟨andGate,i,mem,lo,op⟩ := h
  exact (flat j hj andGate i mem lo op).elim

def linear (C : Circuit) (a b : ℕ) := ∀ k ∈ [a,b], (C.lineDegrees 26 (Finset.Ico 13 26)).getD k 0 ≤ 1

theorem exactMinimum (s : ℕ) :
    (∃ C a b, accepted C a b ∧ linear C a b ∧ C.size ≤ s) ↔ 63 ≤ s := by
  constructor
  · rintro ⟨C,a,b,⟨hm,_,_,_,pos,neg,_⟩,deg,sz⟩
    exact (Linear5198.linearLower C hm a b pos neg deg).trans sz
  · intro hs
    exact ⟨Upper5198.C,29,88,witness,by unfold linear; decide +kernel,hs⟩
end PEqualNP.Outside.Optimum5198
#print axioms PEqualNP.Outside.Optimum5198.exactMinimum
