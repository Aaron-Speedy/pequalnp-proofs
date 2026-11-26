import SignedGraph9750
import Restriction9750
namespace PEqualNP.Outside.Signed9750
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9750_aux (f0)

theorem binaryLower (C : Circuit) (ok : FanInTwo C)
    (ev : ∀ x : Assignment, C.eval (List.ofFn x) = f0 x) : 14 ≤ cost C.gates := by
  let wires : List (Fn Assignment) := List.ofFn (fun i : Fin 12 => fun x => x i)
  have hw : ∀ z ∈ wires, primary z := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact Or.inr ⟨i,Or.inl rfl⟩
  have legal : ∀ g ∈ C.gates, fan g := by
    intro g hg
    obtain ⟨ops,arity⟩ := ok g hg
    exact ⟨by simpa using ops,arity⟩
  have program := comp C.gates C.output legal wires primary stablePrimary hw
  have same : readF (traceF C.gates wires) C.output = table4095_0 := by
    funext y
    rw [← readAt,traceAt]
    have e : wires.map (fun z => z y) = List.ofFn y := by simp [wires,Function.comp_def]
    rw [e]
    exact ev y
  rw [same] at program
  exact lowtable4095_0 _ program

def notCount (gs : List Gate) := (gs.filter (fun g => !useBinary g)).length

theorem countAll (gs : List Gate) : notCount gs + cost gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : useBinary g <;> simp [notCount,cost,h] at * <;> omega

theorem fewNegations (C : Circuit) (ok : FanInTwo C)
    (ev : ∀ x : Assignment, C.eval (List.ofFn x) = f0 x) (size : C.size ≤ 20) :
    notCount C.gates ≤ 6 := by
  have := binaryLower C ok ev
  have := countAll C.gates
  change C.gates.length ≤ 20 at size
  omega

end PEqualNP.Outside.Signed9750
#print axioms PEqualNP.Outside.Signed9750.fewNegations
