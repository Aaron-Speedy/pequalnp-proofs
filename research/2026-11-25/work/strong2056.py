import sys,itertools,tempfile,subprocess
from pathlib import Path
points=tuple(map(int,sys.argv[1].split(',')))
size=int(sys.argv[2]); limit=int(sys.argv[3])
p=len(points); D={0,1,3,9}
cols=[sum(1<<i for i,u in enumerate(points) if (u+v)%13 in D) for v in range(13)]
classes=sorted(set(cols)-{0});n=p+len(classes)
pos=[(1<<i)|(1<<(j+p)) for j,m in enumerate(classes) for i in range(p) if m>>i&1]
negative=[]
for s in range(1<<p):
 row=s|sum(1<<(j+p) for j,m in enumerate(classes) if not m&s)
 negative.append(row)
neg=[x for x in negative if not any(x!=y and x&y==x for y in negative)]
rows=pos+neg
print('points',points,'gates',size,'core variables',n,'tests',len(rows),'prepaid ORs',sum(cols.count(m)-1 for m in classes),flush=True)
nv=0;cl=[]
def var():
 global nv
 nv+=1;return nv
def one(xs):
 cl.append(xs[:])
 prev=0
 for x in xs[:-1]:
  t=var();cl.append([-x,t])
  if prev:cl.extend([[-prev,t],[-prev,-x]])
  prev=t
 cl.append([-prev,-xs[-1]])
V=[[var() for r in rows] for _ in range(n+size)]
for i in range(n):
 for v,r in zip(V[i],rows):cl.append([v if r>>i&1 else -v])
perms=[]
for perm in itertools.permutations(range(p)):
 def move(m):return sum(1<<perm[h] for h in range(p) if m>>h&1)
 if all(move(m) in classes for m in classes):
  perms.append(perm+tuple(p+classes.index(move(m)) for m in classes))
uses=[[] for _ in V]; gates=[];previous=[]
for i in range(n,n+size):
 sel=[[var() for j in range(i)] for _ in range(2)];op=var();gates.append((sel,op))
 args=[[var() for r in rows] for _ in sel]
 for pick,arg in zip(sel,args):
  one(pick)
  for j,q in enumerate(pick):
   uses[j].append(q)
   for a,v in zip(arg,V[j]):cl.extend([[-q,-a,v],[-q,a,-v]])
 for l,x in enumerate(sel[0]):
  for y in sel[1][:l+1]:cl.append([-x,-y])
 for r,x in enumerate(previous):
  for y in sel[1][:r]:cl.append([-x,-y])
 if not previous:
  for a,b in itertools.combinations(range(n),2):
   if (a,b)!=min(tuple(sorted((perm[a],perm[b]))) for perm in perms):
    cl.append([-sel[0][a],-sel[1][b]])
 else:
  prior=gates[-2][0]
  for r in range(len(previous)):
   for a in range(r):
    for b in range(a):
     cl.append([-previous[r],-sel[1][r],-prior[0][a],-sel[0][b]])
 previous=sel[1]
 for ai,bi in ((0,1),(1,0)):
  witnesses=[]
  for a,b in zip(args[ai],args[bi]):
   w=var(); witnesses.append(w); cl.extend([[-w,a],[-w,-b]])
  cl.append(witnesses)
 for a,b,v in zip(*args,V[i]):
  cl.extend([[op,-a,-b,v],[op,a,-v],[op,b,-v],[-op,a,b,-v],[-op,-a,v],[-op,-b,v]])
cl.extend(uses[:-1])
for ix,v in enumerate(V[-1]):cl.append([v if ix<len(pos) else -v])
solver=Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
with tempfile.NamedTemporaryFile(mode='w',suffix='.cnf') as out:
 print('p cnf',nv,len(cl),file=out)
 for c in cl:print(*c,0,file=out)
 out.flush(); cp=subprocess.run([solver,'-q','-t',str(limit),out.name],capture_output=True,text=True)
print('solver',cp.returncode,flush=True)
if cp.returncode==10:
 model={int(x) for line in cp.stdout.splitlines() if line.startswith('v ') for x in line.split()[1:]}
 gs=[(op in model,*[next(i for i,x in enumerate(v) if x in model) for v in sel]) for sel,op in gates]
 print('circuit',gs,flush=True)
 for r in range(1<<n):
  vals=[bool(r>>i&1) for i in range(n)]
  for op,a,b in gs:vals.append((vals[a] or vals[b]) if op else (vals[a] and vals[b]))
  assert vals[-1]==any(r>>i&1 and r>>(p+j)&1 for j,m in enumerate(classes) for i in range(p) if m>>i&1)
 print('all rows verified',flush=True)
