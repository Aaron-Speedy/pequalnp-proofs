import json
from pathlib import Path
from plane10005 import coords,generator
C=coords()
G=[generator(C,M) for M in [[[0,1,0],[0,0,1],[1,0,0]],[[1,1,0],[0,1,0],[0,0,1]],[[2,0,0],[0,1,0],[0,0,1]]]]
giants=[tuple(x) for x in json.loads(Path('.pnp/conics10005.json').read_text())];base=giants[0]
def perm(m,p):
 out=0
 while m:
    v=m&-m;m^=v;out|=1<<p[v.bit_length()-1]
 return out
def act(z,g):return (perm(z[0],g[0]),perm(z[1],g[1]))
def compose(g,h):return tuple(tuple(g[q][i] for i in h[q]) for q in (0,1))
def inv(g):return tuple(tuple(p.index(i) for i in range(31)) for p in g)
identity=(tuple(range(31)),)*2
maps={base:identity};todo=[base];stab=set()
while todo:
 p=todo.pop()
 for g in G:
    v=act(p,g); m=compose(g,maps[p])
    if v not in maps:maps[v]=m;todo.append(v)
    else:stab.add(compose(inv(maps[v]),m))
assert len(maps)==3100
remaining=set(giants[1:]);reps=[]
while remaining:
 p=min(remaining);reps.append(p);orb={p};todo=[p]
 while todo:
    x=todo.pop()
    for g in stab:
        y=act(x,g)
        if y not in orb:orb.add(y);todo.append(y)
 remaining-=orb
print('stabilizer generators',len(stab),'second-rectangle classes',len(reps),flush=True)
src=Path('.pnp/rect10005.cnf').read_text().splitlines()
# Keep the exact coverage and soundness clauses, replacing previous symmetry anchors.
clauses=src[1:1+775*31+186*15]
n=930+775*15
def append(xs):clauses.append(' '.join(map(str,xs))+' 0')
def literals(box,k):
 for side,mask in enumerate(box):
    for i in range(31):
        if mask>>i&1:yield 1+15*(31*side+i)+k
for lit in literals(base,0): append([lit])
sel=[]
for k,bs in enumerate((reps,giants[1:],giants[1:]),1):
 opts=[]
 for box in bs:
    n+=1;v=n;opts.append(v)
    for lit in literals(box,k):append([-v,lit])
 append(opts);sel.append(opts)
prev=None
for v,w in zip(sel[1],sel[2]):
 append(([-w] if prev is None else [-w,prev]))
 n+=1;nv=n
 append([-v,nv])
 if prev is not None:append([-prev,nv]);append([-nv,v,prev])
 else:append([-nv,v])
 prev=nv
for k in range(4,14):
 for r in range(31):append([-(1+15*r+k+1)]+[1+15*s+k for s in range(r+1)])
Path('.pnp/rect10005-anchored.cnf').write_text('p cnf '+str(n)+' '+str(len(clauses))+'\n'+'\n'.join(clauses)+'\n')
