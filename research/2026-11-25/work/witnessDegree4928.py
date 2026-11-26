from degreeEval4928 import evaluate,hits,ns
from pathlib import Path
import json
d=Path('.pnp');gs28,out28=json.loads((d/'fano4126.json').read_text())
def partial():
 gs=[]
 def g(op,a,b):
    gs.append((op,a,b))
    return len(gs)+13
 stars=[]
 for p in range(7):
    ls=[7+l for l in range(7) if (p-l)%7 in (0,1,3) and (p,l)!=(0,0)]
    s=ls[0]
    for v in ls[1:]:s=g(1,s,v)
    stars.append(g(0,p,s))
 h=stars[0]
 for t in stars[1:]:h=g(1,h,t)
 return gs,g(0,g(1,h,0),g(1,h,7))
gs29,out29=partial()
s='''import Normalize4928
import PEqualNP.Outside.L_meta_6371
open PEqualNP.CircuitLowerBounds LocalFano4126 Local4928
namespace Threshold4928
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
'''
for gs,out in [(gs28,out28),(gs29,out29)]:
 k=len(gs);x=evaluate(gs)[out];assert x&((1<<58)-1)==ns['want']
 print(k,len(hits(x)),hits(x))
 s+=f'def C{k} : Circuit := ⟨['+', '.join(f'⟨.{("or" if op else "and")},[{a},{b}]⟩' for op,a,b in gs)+f'],{out}⟩\n'
 s+=f'''theorem legal{k} : Legal C{k} := by
  intro j g h
  obtain ⟨hj,he⟩ := List.getElem?_eq_some_iff.mp h
  let t : Fin C{k}.gates.length := ⟨j,hj⟩
  let ok (op : GateOp) := match op with | .and | .or => true | _ => false
  have spec : ∀ t : Fin C{k}.gates.length, let g := C{k}.gates[t.val]; let a := g.inputs.getD 0 0; let b := g.inputs.getD 1 0;
    ok g.op = true ∧ g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+t.val ∧ b < 14+t.val := by decide +kernel
  obtain ⟨op,rest⟩ := spec t
  subst g
  refine ⟨?_,_,_,rest⟩
  change (C{k}.gates[j]).op = .and ∨ (C{k}.gates[j]).op = .or
  change ok (C{k}.gates[j]).op = true at op
  cases e : (C{k}.gates[j]).op <;> simp_all [ok]
theorem computes{k} (x : Fin 14 → Bool) : C{k}.eval (List.ofFn x) = true ↔ F x := by
  apply exactOf C{k} legal{k} _ _ x
  · unfold Pos; decide +kernel
  · intro y off maximal
    obtain ⟨j,rfl⟩ := PEqualNP.Outside.L_meta_6371 y off maximal
    clear off maximal
    revert j
    decide +kernel
theorem cost{k} : C{k}.size = {k} := rfl
theorem marks{k} : ∀ p l : Fin 7, Both C{k} p l ↔ '''+('p ≠ 2' if k==28 else 'True')+''' := by decide +kernel
'''
s+='end Threshold4928\n'+'\n'.join(f'#print axioms Threshold4928.{a}{k}' for k in [28,29] for a in ['computes','marks'])+'\n'
(d/'WitnessDegree4928.lean').write_text(s)
