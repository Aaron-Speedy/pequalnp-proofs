import sys,subprocess,tempfile
from pathlib import Path
from itertools import combinations
size=int(sys.argv[1]); chosen=int(sys.argv[2]); n=5; rows=32
def target(r):return bool(r&1 and r&20 or r&2 and r&24)
nv=0; clauses=[]
def fresh():
    global nv
    nv+=1;return nv
def one(v):
    clauses.append(v)
    clauses.extend([-a,-b] for a,b in combinations(v,2))
def copy(q,o,i):
    clauses.extend([[-q,-o,i],[-q,o,-i]])
values=[[fresh() for row in range(rows)] for w in range(n+size)]
outs=[fresh() for _ in values];one(outs)
for r in range(rows):
    for i in range(n):
        bit=bool(r&(1<<i))
        clauses.append([values[i][r] if bit else -values[i][r]])
    for q,v in zip(outs,values):clauses.append([-q,v[r] if target(r) else -v[r]])
gates=[]; pre=[]
for j in range(size):
    w=n+j; op=fresh();sel=[[fresh() for i in range(w)] for b in range(2)]
    arg=[[fresh() for r in range(rows)] for b in range(2)]
    for side,vs in zip(sel,arg):
        one(side)
        for i,q in enumerate(side):
            for a,v in zip(vs,values[i]):copy(q,a,v)
    for i,q in enumerate(sel[0]):
        for t in sel[1][:i]:clauses.append([-q,-t])
    for a,b,v in zip(*arg,values[w]):
        clauses.extend([[op,-a,-b,v],[op,a,-v],[op,b,-v],[-op,a,b,-v],[-op,-a,v],[-op,-b,v]])
    gates.append((op,sel,arg))
    ancestor=[]
    for k in range(j):
        children=[]
        for side in sel:
            children.append(side[n+k])
            for p in range(k+1,j):
                h=fresh();q=side[n+p];z=pre[p][k]
                clauses.extend([[-h,q],[-h,z],[h,-q,-z]]);children.append(h)
        u=fresh();clauses.extend([[-c,u] for c in children]);clauses.append([-u]+children);ancestor.append(u)
    pre.append(ancestor)
matches=[]
for i,j in combinations(range(size),2):
    h=fresh();matches.append(h)
    pass
    pass
    for k,r in [(i,1),(j,1<<chosen)]:
        op,sel,arg=gates[k]
        for lit in [-op,values[n+k][1 | (1<<chosen)],-arg[0][r],-arg[1][r]]:clauses.append([-h,lit])
clauses.append(matches)
dirty=[]
for k,(op,_,_) in enumerate(gates):
    for r in range(rows):
        if target(r):continue
        h=fresh();dirty.append(h);clauses.extend([[-h,-op],[-h,values[n+k][r]]])
pass
path=Path('.pnp')/f'loosePair5208-{size}-{chosen}.cnf'
with path.open('w') as f:
    print('p cnf',nv,len(clauses),file=f)
    for c in clauses:print(*c,0,file=f)
solver=Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
result=subprocess.run([solver,'-q','-t','180',str(path)],capture_output=True,text=True)
print('gates',size,'SAT solver exit',result.returncode,flush=True)
if result.returncode==10:
    model={int(x) for line in result.stdout.splitlines() if line.startswith('v ') for x in line.split()[1:]}
    circuit=[(op in model,*[next(i for i,q in enumerate(side) if q in model) for side in sel]) for op,sel,_ in gates]
    print(circuit)
    for r in range(rows):
        v=[bool(r>>i&1) for i in range(n)]
        for op,a,b in circuit:v.append(v[a]|v[b] if op else v[a]&v[b])
        assert v[next(i for i,z in enumerate(outs) if z in model)]==target(r)
