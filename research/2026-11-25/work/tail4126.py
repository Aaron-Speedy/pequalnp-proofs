from pathlib import Path
from itertools import combinations
import subprocess,sys,tempfile,json
ns={};exec(Path('.pnp/nearFano4126.py').read_text().split('for r in (2,4,5,6)')[0],ns)
cut=int(sys.argv[1]);r=int(sys.argv[2]);chain=int(sys.argv[3]);reverse=int(sys.argv[4]);limit=int(sys.argv[5])
orig=ns['seed'](r,chain,reverse);prefix=orig[:-cut];start=ns['evaluate'](prefix);size=cut-(0 if len(sys.argv)>6 else 1);nbits=62;nv=0;c=[]
def var():
 global nv
 nv+=1;return nv
def one(xs):
 c.append(xs)
 for a,b in combinations(xs,2):c.append([-a,-b])
def And(v,a,b):c.extend([[-a,-b,v],[a,-v],[b,-v]])
def Or(v,a,b):c.extend([[a,b,-v],[-a,v],[-b,v]])
def mux(q,v,a,b):c.extend([[-q,-a,v],[-q,a,-v],[q,-b,v],[q,b,-v]])
values=[[var() for _ in range(nbits)] for _ in range(len(start)+size)]
for n,vs in zip(start,values):
 for i,v in enumerate(vs):c.append([v if n>>i&1 else -v])
gates=[]
for k in range(size):
 m=len(start)+k;op=var(); pins=[[var() for _ in range(m)] for _ in range(2)]
 arg=[[var() for _ in range(nbits)] for _ in range(2)]
 for side,cols in zip(pins,arg):
  one(side)
  for q,other in zip(side,values):
   for z,a in zip(cols,other):c.extend([[-q,-z,a],[-q,z,-a]])
 for i,u in enumerate(pins[0]):
  for v in pins[1][:i+1]:c.append([-u,-v])
 # Order independent gates by their larger parent; use the new tail only.
 if gates:
  for i,u in enumerate(gates[-1][1][1]):
   for v in pins[1][:i]:c.append([-u,-v])
 for i,(a,b,v) in enumerate(zip(*arg,values[m])):
  if i in (59,61):
   x,y,z=var(),var(),var()
   And(x,arg[0][i-1],b);And(y,a,arg[1][i-1]);Or(z,x,y)
   c.extend([[op,-z,v],[op,z,-v]])
  else:c.extend([[op,-a,-b,v],[op,a,-v],[op,b,-v]])
  c.extend([[-op,a,b,-v],[-op,-a,v],[-op,-b,v]])
 gates.append((op,pins))
for i,v in enumerate(values[-1]):c.append([v if ns['want']>>i&1 else -v])
solver=Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
with tempfile.NamedTemporaryFile(mode='w') as f:
 print('p cnf',nv,len(c),file=f)
 for cl in c:print(*cl,0,file=f)
 f.flush();run=subprocess.run([solver,'-q','-t',str(limit),f.name],capture_output=True,text=True)
print('removed',cut,'point',r,'chain',chain,'reverse',reverse,'budget',size,'exit',run.returncode,flush=True)
if run.returncode==10:
 model={int(x) for l in run.stdout.splitlines() if l.startswith('v ') for x in l.split()[1:]}
 tail=[(int(op in model),*[next(i for i,q in enumerate(s) if q in model) for s in pins]) for op,pins in gates]
 gs=prefix+tail
 assert ns['evaluate'](gs)[-1]==ns['want'] and len(gs)==len(prefix)+size
 if len(gs)==27:Path('.pnp/fano27-tail.json').write_text(json.dumps([gs,40]))
 print('found verified packed witness')
