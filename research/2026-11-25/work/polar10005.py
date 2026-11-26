from plane10005 import *
from collections import Counter
c=coords()
lookup={l:j for j,l in enumerate(lines)}
pol=[lookup[frozenset(i for i,a in c.items() if sum(x*y for x,y in zip(a,c[v]))%5==0)] for v in range(31)]
assert all((rows[i]>>pol[j]&1)==(rows[j]>>pol[i]&1) for i in range(31) for j in range(31))
adj=[sum(1<<j for j in range(31) if i!=j and not rows[i]>>pol[j]&1) for i in range(31)]
hist=Counter()
cliques=[]
def enum(s,rem):
    hist[s.bit_count()]+=1
    if not rem:cliques.append(s)
    while rem:
        bit=rem&-rem;rem^=bit
        enum(s|bit,rem&adj[bit.bit_length()-1])
enum(0,sum(1<<i for i in range(31) if not rows[i]>>pol[i]&1))
print('selfdual rectangle counts by side size:',sorted(hist.items()))
Path('.pnp/polar10005.json').write_text(json.dumps(pol))
