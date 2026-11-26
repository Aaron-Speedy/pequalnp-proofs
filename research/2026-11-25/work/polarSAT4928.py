from pathlib import Path
from itertools import combinations
import subprocess,sys,tempfile,json
from degreeEval4928 import ns,evaluate,good,hits
cut=int(sys.argv[1]);r=int(sys.argv[2]);chain=int(sys.argv[3]);reverse=int(sys.argv[4]);limit=int(sys.argv[5])
orig=ns['seed'](r,chain,reverse);prefix=orig[:-cut];start=evaluate(prefix);size=cut-(0 if len(sys.argv)>6 else 1);nbits=86;nv=0;c=[]
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
  if 58<=i<72:
   Or(v,a,b)
   continue
  if i>=72:
   prod=var();either=var();both=var()
   And(prod,arg[0][i-14],arg[1][i-14]);Or(either,a,b);Or(both,either,prod)
   mux(op,v,either,both)
   continue
  else:c.extend([[op,-a,-b,v],[op,a,-v],[op,b,-v]])
  c.extend([[-op,a,b,-v],[-op,-a,v],[-op,-b,v]])
 # In a size-minimal circuit both input signatures must have a distinguishing
 # boundary assignment in each direction. Otherwise AND or OR repeats a parent.
 for left,right in ((0,1),(1,0)):
  witness=[]
  for i in range(58):
   q=var();witness.append(q)
   c.extend([[-q,arg[left][i]],[-q,-arg[right][i]]])
  c.append([-op]+witness[:21]);c.append([op]+witness[21:])
 for prev in range(m):
  distinguishing=[]
  for i,z in enumerate(values[m][:58]):
   positive=i<21
   if prev<len(start) and bool(start[prev]>>i&1)==positive:continue
   q=var();distinguishing.append(q)
   c.append([-q,z if positive else -z])
   if prev>=len(start):c.append([-q,-values[prev][i] if positive else values[prev][i]])
  c.append(distinguishing)
 gates.append((op,pins))
for i,v in enumerate(values[-1][:58]):c.append([v if ns['want']>>i&1 else -v])
flags=[]
for p in range(7):
 for l in range(7):
  if (p-l)%7 in (0,1,3):
   v=var();And(v,values[-1][72+p],values[-1][79+l]);flags.append(v)
c.append(flags)
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
 assert good(evaluate(gs)[-1]) and len(gs)==len(prefix)+size
 if len(gs)==27:Path('.pnp/fano27-degree4928.json').write_text(json.dumps([gs,40]))
 print('found verified packed witness')
