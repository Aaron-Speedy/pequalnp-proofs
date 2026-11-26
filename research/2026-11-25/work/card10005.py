"""Symmetry breaking for any specified minimum number of large rectangles."""
import json,sys
from pathlib import Path
G=int(sys.argv[1])
A=lambda r,k:1+15*r+k
B=lambda j,k:1+15*(31+j)+k
base=json.loads(Path('.pnp/conics10005.json').read_text())[0]
clauses=[]
with open('.pnp/rect10005.cnf') as f:
    n=int(next(f).split()[2])
    old=[next(f) for _ in range(775*31+186*15)]
def fresh():
    global n
    n+=1
    return n
def counts(xs):
    # d[j] means at least j of the inputs seen so far are true.
    prev=[True]+[False]*10
    def neg(x):return not x if type(x) is bool else -x
    def put(*lits):
        if True in [x for x in lits if type(x) is bool]:return
        clauses.append([x for x in lits if type(x) is int])
    for x in xs:
        d=[True]
        for j in range(1,11):
            u,v=prev[j],prev[j-1]
            t=fresh();d.append(t)
            put(neg(u),t);put(neg(v),-x,t)
            put(-t,u,v);put(-t,u,x)
        prev=d
    return prev
for side,fn in zip(base,[A,B]):
    for i in range(31):
        x=fn(i,0)
        clauses.append([x if side>>i&1 else -x])
flags=[]
for k in range(1,G):
    a,b=[counts([fn(i,k) for i in range(31)]) for fn in (A,B)]
    flag=fresh();flags.append(flag)
    clauses.extend([[a[6]],[b[6]],[-flag,a[10]],[flag,b[10]]])
for x,y in zip(flags,flags[1:]):clauses.append([x,-y])
for lo,hi in [(1,G-1),(G,14)]:
    for k in range(lo,hi):
        guards=[[flags[k-1],flags[k]],[-flags[k-1],-flags[k]]] if lo==1 else [[]]
        for guard in guards:
            for r in range(31):clauses.append(guard+[-A(r,k+1)]+[A(s,k) for s in range(r+1)])
with open(f'.pnp/card10005-{G}.cnf','w') as out:
    print('p cnf',n,len(old)+len(clauses),file=out)
    out.writelines(old)
    for cl in clauses:print(*cl,0,file=out)
