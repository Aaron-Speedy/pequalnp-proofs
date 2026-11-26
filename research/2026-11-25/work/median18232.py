from pathlib import Path
pairs=[(0,7),(1,2),(3,5),(4,8),(0,2),(1,5),(3,8),(4,7),(0,3),(1,4),(2,8),(5,7),(3,4),(5,6),(2,5),(4,6),(2,3),(4,5),(3,4)]
w=list(range(9)); gates=[]
for i,j in pairs:
    a,b=w[i],w[j]
    w[i],w[j]=9+len(gates),10+len(gates)
    gates.extend([('and',a,b),('or',a,b)])
keep={w[4]}
for t in reversed(range(len(gates))):
    if 9+t in keep: keep.update(gates[t][1:])
idx={v:i for i,v in enumerate(sorted(keep))}
assert len(idx)==39
gs=[(op,idx[a],idx[b]) for t,(op,a,b) in enumerate(gates) if t+9 in keep]
for x in range(512):
    bits=[bool(x>>i&1) for i in range(9)]
    for op,a,b in gs: bits.append(bits[a] and bits[b] if op=='and' else bits[a] or bits[b])
    assert bits[-1]==(x.bit_count()>=5)
names=list('abcdefghi')
expr=names.copy()
for op,a,b in gs: expr.append('('+expr[a]+(' && ' if op=='and' else ' || ')+expr[b]+')')
path=Path('lean/PEqualNP/Outside/L_meta_18232.lean')
stmt=next(line for line in path.read_text().splitlines() if line.startswith('theorem PEqualNP.Outside.L_meta_18232 :'))
ns='PEqualNP.Outside.L_meta_18232_aux'
vec='['+', '.join(names)+']'
s='''import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace '''+ns+'''

-- The nine-input median network from Bert Dobbelaere's median network list.
-- Each retained low output is an AND and each high output is an OR.
-- https://bertdobbelaere.github.io/median_networks.html#N9L19D7
def network : Circuit :=
  ⟨['''+',\n    '.join('⟨.'+op+', ['+str(a)+', '+str(b)+']⟩' for op,a,b in gs)+'''], 38⟩

theorem correct (a b c d e f g h i : Bool) :
    network.eval '''+vec+' = decide (5 ≤ '+vec+'''.count true) := by
  change '''+expr[-1]+''' = _
  revert a b c d e f g h i
  decide

end '''+ns+'\n\nopen '+ns+'\n\n'+stmt+'''
  refine ⟨network, ?_, by decide, fun x => ?_⟩
  · simp [FanInTwo, network]
  · exact correct (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
'''
path.write_text(s)
