import json
from pathlib import Path
d=Path('.pnp');g,out,_,_=json.loads((d/'marked5208.json').read_text())
s='''import Reflect5208
open PEqualNP.CircuitLowerBounds
namespace Marked5208
open Reflection
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000
def partialDNF (i : ℕ) := (C.gates.take i).foldl sym init
theorem advance (i : ℕ) (hi : i < C.gates.length) :
    partialDNF (i+1) = sym (partialDNF i) C.gates[i] := by
  unfold partialDNF
  rw [List.take_succ_eq_append_getElem hi,List.foldl_append]
  rfl
def t0 := init
theorem r0 : partialDNF 0 = t0 := rfl
'''
vals=[{frozenset([i])} for i in range(26)]
def lit(t):return '{'+','.join(map(str,sorted(t)))+'}'
for i,(op,a,b) in enumerate(g):
 f=vals[a]|vals[b] if op else {x|y for x in vals[a] for y in vals[b]}
 vals.append(f);n=i+1
 s+=f'def z{n} : DNF := '+'{'+','.join(lit(t) for t in sorted(f,key=lambda x:tuple(sorted(x))))+'}\n'
 s+=f'def t{n} := t{i} ++ [z{n}]\n'
 s+=f'theorem r{n} : partialDNF {n} = t{n} := by\n  rw [advance {i} (by decide),r{i}]\n'
 s+=f'  apply congrArg (fun m : DNF => t{i} ++ [m])\n  decide +kernel\n'
s+='''theorem allTerms : result = z66 := by
  have eq : C.gates.take 66 = C.gates := List.take_of_length_le (by decide)
  have h := r66
  unfold partialDNF at h
  rw [eq] at h
  unfold result
  rw [h]
  rfl
end Marked5208
#print axioms Marked5208.allTerms
'''
(d/'TableCert5208.lean').write_text(s)
s=(d/'Witness5208.lean').read_text().replace('import Reflect5208','import TableCert5208').replace('⊆ t := by decide +kernel','⊆ t := by rw [allTerms]; decide +kernel').replace('E p l ∈ result := by decide +kernel','E p l ∈ result := by rw [allTerms]; decide +kernel')
(d/'TableWitness5208.lean').write_text(s)
