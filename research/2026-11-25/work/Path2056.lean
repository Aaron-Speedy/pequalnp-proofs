import CheckAdapter2056
import MonoPin9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.BlockProof2056
open PEqualNP.Outside.MonoPin9738
namespace PEqualNP.Outside.Path2056

def path (x : Fin 4 → Bool) := (x 0 && x 3) || (x 1 && (x 2 || x 3))
def bank : List Word := [43690,52428,61680,65280]
def rows (r : Fin 16) (i : Fin 4) := r.val.testBit i.val
def signature : Word := 61120
set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem pathLower (C : Circuit) (hm : Monotone2 C) (he : ∀ x, C.eval (List.ofFn x) = path x) :
    4 ≤ C.size := exclude bank signature (by decide) rows path (by decide +kernel) (by decide +kernel)
      (by decide +kernel : safe signature 3 (0::BitVec.allOnes 16::bank) = true) C hm he

theorem lower (C : Circuit) (mono : Monotone2 C) (ev : ∀ x, C.eval (List.ofFn x) = block x) : 5 ≤ C.size := by
  let g := fun x : Fin 5 → Bool => (x 0 && x 4) || (x 1 && (x 3 || x 4))
  let a : Fin 5 → Bool := ![true,false,false,false,false]
  let b : Fin 5 → Bool := ![true,false,true,false,false]
  let u : Fin 5 → Bool := fun _ => false
  let v : Fin 5 → Bool := fun _ => true
  have hc : MSize 5 block C.size := ⟨C,mono,le_rfl,ev⟩
  have restr : ∀ x, block (Function.update x 2 false) = g x := by
    intro x
    simp [block,g,Function.update_of_ne,show (0:Fin 5)≠2 by decide,show (1:Fin 5)≠2 by decide,
      show (3:Fin 5)≠2 by decide,show (4:Fin 5)≠2 by decide]
  obtain ⟨t,ht,sm⟩ := pin block g 2 a b u v (by decide) (by decide) (by decide) restr hc
  let π : Fin 5 → Fin 4 := ![0,1,0,2,3]
  obtain ⟨D,hm,hs,he⟩ := relabel_size π g t sm
  have low := pathLower D hm (fun x => he x)
  omega
end PEqualNP.Outside.Path2056
#print axioms PEqualNP.Outside.Path2056.lower
