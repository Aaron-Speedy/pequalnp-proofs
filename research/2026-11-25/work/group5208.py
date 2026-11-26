import sys,subprocess,tempfile
from pathlib import Path
from itertools import combinations
size=int(sys.argv[1]); chosen=int(sys.argv[2]); shape=sys.argv[3]
groups={'triple':[[3,6],[4,6],[5,6]],'triangle':[[3,6,7],[4,6,8],[5,7,8]],
        'quad':[[4,8],[5,8],[6,8],[7,8]]}[shape]
n=1+max(max(ns) for ns in groups);points=len(groups)
def target(r):
    return any((r>>p&1) and any(r>>l&1 for l in ns) for p,ns in enumerate(groups))
positives=[(1<<p)|(1<<l) for p,ns in enumerate(groups) for l in ns]
negatives=[]
for pm in range(1<<points):
    off=sum(1<<l for l in range(points,n) if all(not(pm>>p&1) or l not in ns for p,ns in enumerate(groups)))
    negatives.append(pm|off)
rows=sorted(set(positives+negatives+[1,1<<chosen]))
index={r:i for i,r in enumerate(rows)}
nv=0; clauses=[]
def fresh():
    global nv
    nv+=1;return nv
def one(v):
    clauses.append(v)
    clauses.extend([-a,-b] for a,b in combinations(v,2))
def copy(q,o,i):
    clauses.extend([[-q,-o,i],[-q,o,-i]])
values=[[fresh() for row in rows] for w in range(n+size)]
for r in rows:
    for i in range(n):
        bit=bool(r&(1<<i))
        clauses.append([values[i][index[r]] if bit else -values[i][index[r]]])
    clauses.append([values[-1][index[r]] if target(r) else -values[-1][index[r]]])
gates=[]; pre=[]
for j in range(size):
    w=n+j; op=fresh();sel=[[fresh() for i in range(w)] for b in range(2)]
    arg=[[fresh() for r in rows] for b in range(2)]
    for side,vs in zip(sel,arg):
        one(side)
        for i,q in enumerate(side):
            for a,v in zip(vs,values[i]):copy(q,a,v)
    for i,q in enumerate(sel[0]):
        for t in sel[1][:i+1]:clauses.append([-q,-t])
    for a,b,v in zip(*arg,values[w]):
        clauses.extend([[op,-a,-b,v],[op,a,-v],[op,b,-v],[-op,a,b,-v],[-op,-a,v],[-op,-b,v]])
    if gates:
        prev=gates[-1][1]
        for i,q in enumerate(prev[1]):
            for t in sel[1][:i]:clauses.append([-q,-t])
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
    clauses.append([-h,pre[j][i]])
    if j<size-1:clauses.append([-h,pre[-1][j]])
    for k,r in [(i,1),(j,1<<chosen)]:
        op,sel,arg=gates[k]
        for lit in [-op,values[n+k][index[1 | (1<<chosen)]],-arg[0][index[r]],-arg[1][index[r]]]:clauses.append([-h,lit])
clauses.append(matches)
dirty=[]
for k,(op,_,_) in enumerate(gates):
    for r in rows:
        if target(r):continue
        h=fresh();dirty.append(h);clauses.extend([[-h,-op],[-h,values[n+k][index[r]]]])
clauses.append(dirty)
path=Path('.pnp')/f'group5208-{shape}-{size}-{chosen}.cnf'
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
    rows=range(1<<n)
    def sim(row):
        v=[bool(row>>i&1) for i in range(n)]
        for op,a,b in circuit:v.append(v[a]|v[b] if op else v[a]&v[b])
        return v
    cones=[set() for _ in range(n)]
    for op,a,b in circuit:cones.append(cones[a]|cones[b]|{a,b})
    ok=lambda k,r: (not circuit[k][0] and sim(1|1<<chosen)[n+k] and
        all(not sim(r)[i] for i in circuit[k][1:]))
    assert any(n+i in cones[n+j] and (n+j in cones[-1] or j==size-1) and ok(i,1) and ok(j,1<<chosen)
        for i,j in combinations(range(size),2))
    assert any(not target(r) and any(not op and sim(r)[n+k]
        for k,(op,a,b) in enumerate(circuit)) for r in rows)
    for r in rows:
        v=[bool(r>>i&1) for i in range(n)]
        for op,a,b in circuit:v.append(v[a]|v[b] if op else v[a]&v[b])
        assert v[-1]==target(r)
