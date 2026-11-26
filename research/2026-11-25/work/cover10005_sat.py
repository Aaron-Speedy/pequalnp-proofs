"""Exact 15-rectangle membership encoding with a certified incompatible-cell anchor."""
from pathlib import Path
import random,json
rows=json.loads(Path('.pnp/rect10005-rows.json').read_text())
cells=[(r,c) for r in range(31) for c in range(31) if not rows[r]>>c&1]
def clash(a,b):
 r,c=a;s,d=b;return (rows[r]>>d | rows[s]>>c)&1
adj=[sum(1<<i for i,b in enumerate(cells) if clash(a,b)) for a in cells]
rng=random.Random(10005)
best=[]
for _ in range(2800):
 S=(1<<len(cells))-1; clique=[]
 while S:
    ids=[];p=S
    while p:
        v=p&-p;p^=v;ids.append(v.bit_length()-1)
    i=max(rng.sample(ids,min(12,len(ids))),key=lambda i:(adj[i]&S).bit_count()+rng.randrange(4))
    clique.append(i);S &= adj[i]
 if len(clique)>len(best):best=clique
print('clique',len(best),[cells[i] for i in best],flush=True)
assert all(clash(cells[i],cells[j]) for k,i in enumerate(best) for j in best[k+1:])
A=lambda r,k:1+15*r+k
B=lambda j,k:1+15*(31+j)+k
n=930
clauses=[]
for i in range(31):
 for j in range(31):
    if rows[i]>>j&1:
        clauses.extend([[-A(i,k),-B(j,k)] for k in range(15)])
    else:
        options=[]
        for k in range(15):
            n+=1;options.append(n)
            clauses.extend([[-n,A(i,k)],[-n,B(j,k)]])
        clauses.append(options)
for k,v in enumerate(best):
 r,c=cells[v];clauses.extend([[A(r,k)],[B(c,k)]])
# Symmetry breaking among unused colors via nonincreasing first covered row.
for k in range(len(best),14):
 for r in range(31):clauses.append([-A(r,k+1)]+[A(s,k) for s in range(r+1)])
with Path('.pnp/rect10005.cnf').open('w') as f:
 print('p cnf',n,len(clauses),file=f)
 for c in clauses:print(*c,0,file=f)
