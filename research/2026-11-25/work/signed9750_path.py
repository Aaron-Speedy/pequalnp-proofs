from pathlib import Path
from functools import lru_cache
from graph_restrict9750 import edges
G=edges(Path('lean/PEqualNP/Outside/L_meta_9750.lean').read_text())
N=12
adj=[sum(1<<b for b in range(N) if tuple(sorted((a,b))) in G) for a in range(N)]
def vs(x):return [i for i in range(N) if x>>i&1]
from itertools import combinations
paths=[]
for t in combinations(range(N),4):
    m=sum(1<<i for i in t)
    if sorted((adj[i]&m).bit_count() for i in t)==[1,1,2,2]:paths.append(m)
def norm(S,L):
    S &= ~L
    return sum(1<<i for i in vs(S) if adj[i]&S),L
@lru_cache(None)
def tree(S,L):
    U=S|L
    if not U:return (0,'const')
    best=(U.bit_count()-1+int(any(S & t==t for t in paths)),'inputs')
    for i in vs(U):
        if L>>i&1:
            a,b=norm(S,L^(1<<i))
            if a|b:best=max(best,(tree(a,b)[0]+1,f'single {i}'))
            continue
        a=norm(S^(1<<i),L); b=norm(S^(1<<i),L|(adj[i]&S))
        if a[0]|a[1]:
            u=tree(*a)[0];v=tree(*b)[0]
            for k,op in [(u+1,'zero'),(v+1,'one'),(min(u,v)+2,'both')]:best=max(best,(k,f'{op} {i}'))
    return best
if __name__=='__main__':print(tree((1<<N)-1,0),tree.cache_info())
