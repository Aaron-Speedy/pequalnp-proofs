from plane10005 import *
from collections import deque
import re
c=coords()
generators=[generator(c,M) for M in [
 [[0,1,0],[0,0,1],[1,0,0]], [[1,1,0],[0,1,0],[0,0,1]], [[2,0,0],[0,1,0],[0,0,1]]]]
def pm(m,p):
    x=0
    while m:
        a=m&-m;m-=a;x|=1<<p[a.bit_length()-1]
    return x
def dual():
    cf={norm(v):k for k,v in c.items()}
    lookup={l:j for j,l in enumerate(lines)}
    p=[lookup[frozenset(i for i,a in c.items() if sum(x*y for x,y in zip(a,c[v]))%5==0)] for v in range(31)]
    q=[p.index(j) for j in range(31)]
    return p,q
p,q=dual()
big=[]
for line in Path('.pnp/rect10005.dat').open():
    a,b=map(int,line.split())
    if a.bit_count()*b.bit_count()==60:big.append((a,b))
base=next(z for z in big if z[0].bit_count()==6)
todo=[base];seen=set(todo)
while todo:
    a,b=todo.pop()
    candidates=[(pm(a,u),pm(b,v)) for u,v in generators]+[(pm(b,q),pm(a,p))]
    for x in candidates:
        if x not in seen:seen.add(x);todo.append(x)
assert seen==set(big)
print('single orbit',len(seen),'canonical rectangle',base,flush=True)
Path('.pnp/conics10005.json').write_text(json.dumps([base]+[x for x in big if x!=base]))
