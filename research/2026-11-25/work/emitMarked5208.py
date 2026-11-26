from marked5208 import g,out,D
from pathlib import Path
d=Path('.pnp'); t=(d/'Upper5198.lean').read_text()
s='''import MonoPin9738
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.MonoPin9738 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
namespace Marked5208
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def D : Finset (Fin 13) := {0,1,3,9}
def edges : List (Fin 13 × Fin 13) := ['''+','.join(f'({p},{l})' for p in range(13) for l in range(13) if (p-l)%13 in D)+']\n'
s+='def C : Circuit := ⟨['+',\n'.join('⟨.'+('or' if op else 'and')+f',[{a},{b}]⟩' for op,a,b in g)+f'],{out}⟩\n'
s+=t[t.index('def val '):t.index('set_option maxRecDepth',t.index('def val '))]
s+=f'theorem evalu (x : Fin 26 → Bool) : val x {out} = edges.any (fun e => x (Fin.castAdd 13 e.1) && x (Fin.natAdd 13 e.2)) := by\n'
for i in range(26):s+=f'  have h{i} : val x {i} = x {i} := val_input x ({i} : Fin 26)\n'
for j,(op,a,b) in enumerate(g):
 i=26+j
 s+=f'  have h{i} := step_'+('or' if op else 'and')+f' x {j} {a} {b} (by decide) rfl (by decide) (by decide)\n  change val x {i} = _ at h{i}\n'
 if j==4:s+='  have first : val x 30 = x 13 := by rw [h30,h26,h13,h14]; cases x 13 <;> rfl\n'
 if j==9:s+='  have second : val x 35 = val x 34 := by rw [h35,h34,h0]; cases x 0 <;> rfl\n'
s+='  simp only [first,second,'+','.join('h'+str(i) for i in range(26+len(g)) if i not in (30,35))+']\n  simp [edges,Bool.and_or_distrib_left,Bool.or_assoc,Fin.natAdd,Fin.castAdd]\n'
s+='''theorem semantic (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 13, p-l ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  change val x 91 = true ↔ _
  rw [evalu,List.any_eq_true]
  have inc : ∀ p l : Fin 13, (p,l) ∈ edges ↔ p-l ∈ D := by decide +kernel
  constructor
  · rintro ⟨⟨p,l⟩,e,h⟩
    exact ⟨p,l,(inc p l).mp e,Bool.and_eq_true_iff.mp h⟩
  · rintro ⟨p,l,e,h⟩
    exact ⟨(p,l),(inc p l).mpr e,Bool.and_eq_true_iff.mpr h⟩

end Marked5208
#print axioms Marked5208.semantic
'''
(d/'Marked5208.lean').write_text(s)
