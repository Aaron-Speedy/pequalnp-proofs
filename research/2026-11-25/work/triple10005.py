from pathlib import Path
from plane10005 import *
from collections import deque
import random
c=coords()
gen=[generator(c,M) for M in [[[0,1,0],[0,0,1],[1,0,0]],[[1,1,0],[0,1,0],[0,0,1]],[[2,0,0],[0,1,0],[0,0,1]]]]
pivot=(0,next(j for j in range(31) if not rows[0]>>j&1))
seen={pivot};q=deque(seen)
while q:
    a,b=q.popleft()
    for r,l in gen:
        z=r[a],l[b]
        if z not in seen:seen.add(z);q.append(z)
assert len(seen)==775
def clash(x,y):
    r,c=x;s,d=y
    return (rows[r]>>d|rows[s]>>c)&1
cells=sorted(x for x in seen if clash(x,pivot))
adj=[{j for j,b in enumerate(cells) if clash(a,b)} for a in cells]
rng=random.Random(10005)
best=[]
for _ in range(1200):
    cand=set(range(len(cells)));sel=[]
    while cand:
        i=max(rng.sample(sorted(cand),min(10,len(cand))),key=lambda u:len(cand&adj[u])+rng.randrange(3))
        sel.append(i);cand&=adj[i]
    if len(sel)>len(best):best=sel
clique=[cells[i] for i in best]
assert all(clash(x,pivot) for x in clique) and all(clash(x,y) for i,x in enumerate(clique) for y in clique[i+1:])
print('triple anchor',pivot,'adjacent incompatible representatives',clique,flush=True)
A=lambda r,k:1+15*r+k
B=lambda j,k:1+15*(31+j)+k
new=[]
for k,(r,j) in enumerate([pivot]*3+clique):
    new.extend([[A(r,k)],[B(j,k)]])
for lo,hi in [(0,2),(3+len(clique),14)]:
    for k in range(lo,hi):
        for r in range(31):new.append([-A(r,k+1)]+[A(s,k) for s in range(r+1)])
nbase=775*31+186*15
with open('.pnp/rect10005.cnf') as src,open('.pnp/rect10005-triple.cnf','w') as dest:
    n=int(src.readline().split()[2]); print('p cnf',n,nbase+len(new),file=dest)
    for _ in range(nbase):dest.write(next(src))
    for clause in new:print(*clause,0,file=dest)
