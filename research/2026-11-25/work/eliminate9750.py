"""Evaluate a first-gate elimination recurrence on the induced subgraphs."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import json
from graph_restrict9750 import edges,embed,catalog
N=12
graph=edges(Path('lean/PEqualNP/Outside/L_meta_9750.lean').read_text())
adj=[sum(1<<b for b in range(N) if tuple(sorted((a,b))) in graph) for a in range(N)]
def vertices(mask):return [i for i in range(N) if mask>>i&1]
def core(mask):return sum(1<<i for i in vertices(mask) if adj[i]&mask)
known={}
# Map every recorded eight-vertex instance onto every matching induced subset.
for n,E,L,f in catalog():
    if n>12 or L<=n-1:continue
    for S in combinations(range(N),n):
        H={(a,b) for a,b in combinations(range(n),2) if tuple(sorted((S[a],S[b]))) in graph}
        if len(H)!=len(E):continue
        if embed(n,E,n,H):
            mask=sum(1<<i for i in S)
            known[mask]=max(known.get(mask,0),L)
weak={}
@lru_cache(None)
def solve(S):
    vs=vertices(S); n=len(vs)
    if n<2:return 0
    base=max(n-1,known.get(S,0))
    def reduce(i,other=-1,bonus=True):
        T=core(S & ~(1<<i))
        if not T:return 0
        k=solve(T)+n-T.bit_count()
        if other>=0 and not (T>>other&1):return k
        return k+int(bonus)
    for i in vs:base=max(base,reduce(i,bonus=False))
    scores=[]
    for v in vs:scores.append((reduce(v),'not',v))
    for i,j in combinations(vs,2):
        for op in ('and','or'):
            def independent(a,b):
                if op=='and':return bool(adj[a]&S&~(1<<b))
                return bool((adj[a]&S)&~adj[b])
            scores.append((max(reduce(i,j,independent(i,j)),reduce(j,i,independent(j,i))),op,i,j))
    weak[S]=sorted(scores)
    return max(base,min(scores)[0])
full=(1<<N)-1
print('known masks',len(known),'bound',solve(full),'root cases',weak[full][:12],flush=True)
print('one deletion',[(i,solve(core(full^(1<<i)))) for i in range(N)])
