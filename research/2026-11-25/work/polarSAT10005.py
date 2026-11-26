from polar10005 import *
import sys
fixed=int(sys.argv[1])
pairs=(15-fixed)//2
n=0
cnf=[]
def new():
    global n
    n+=1
    return n
def row():return [new() for i in range(31)]
F=[row() for _ in range(fixed)]
AB=[(row(),row()) for _ in range(pairs)]
for i in range(31):
    for j in range(i,31):
        inc=rows[i]>>pol[j]&1
        bs=[(S[i],S[j]) for S in F]+[(u,v) for A,B in AB for u,v in [(A[i],B[j]),(A[j],B[i])]]
        if inc:
            for x,y in bs:cnf.append([-x,-y])
        else:
            options=[]
            for x,y in set(bs):
                if x==y:options.append(x)
                else:
                    t=new();cnf.extend([[-t,x],[-t,y]]);options.append(t)
            cnf.append(options)
# At least two giant pairs. Orient each with its smaller side first.
# Every such rectangle is listed exactly once in the six-point orientation.
inv=[pol.index(j) for j in range(31)]
def transport(mask,perm):return sum(1<<perm[i] for i in range(31) if mask>>i&1)
giants=[(r,transport(l,inv)) for r,l in json.loads(Path('.pnp/conics10005.json').read_text()) if r.bit_count()==6]
# Orthogonal transformations preserve this polarity. Signed permutations of axes
# and reflections in anisotropic vectors generate usable symmetry orbits.
I=[[int(i==j) for j in range(3)] for i in range(3)]
gens=[]
for v in c.values():
    d=sum(x*x for x in v)%5
    if not d:continue
    mat=[[int(i==j)-2*pow(d,-1,5)*v[i]*v[j] for j in range(3)] for i in range(3)]
    P,L=generator(c,mat)
    assert all(pol[P[i]]==L[pol[i]] for i in range(31))
    gens.append(P)
remain=set(giants);reps=[]
while remain:
    rep=min(remain);reps.append(rep);seen={rep};todo=[rep]
    while todo:
        a,b=todo.pop()
        for g in gens:
            z=transport(a,g),transport(b,g)
            if z not in seen:seen.add(z);todo.append(z)
    assert seen<=remain
    remain-=seen
print('giant orbit representatives',len(reps),flush=True)
def select(candidates,slots):
    opts=[]
    for cand in candidates:
        v=new();opts.append(v)
        for mask,S in zip(cand,slots):
            for i in range(31):
                if mask>>i&1:cnf.append([-v,S[i]])
    cnf.append(opts)
count=5 if fixed==3 else 2
for i in range(count):select(reps if i==0 else giants,AB[i])
if fixed==3:
    sevens=[(s,) for s in cliques if s.bit_count()==7]
    assert len(sevens)==420
    for S in F:select(sevens,[S])
for group in [F,[a for a,b in AB[1:count]],[a for a,b in AB[count:]]]:
    for a,b in zip(group,group[1:]):
        for i in range(31):cnf.append([-b[i],*a[:i+1]])
p=Path('.pnp/polar10005-'+str(fixed)+'.cnf')
with p.open('w') as f:
    print('p cnf',n,len(cnf),file=f)
    for cl in cnf:print(*cl,0,file=f)
print(n,len(cnf),flush=True)
