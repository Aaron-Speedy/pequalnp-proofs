from itertools import combinations
from pathlib import Path
import json,sys,time
D={0,1,3,9}
N=[sum(1<<j for j in range(13) if (i+j)%13 in D) for i in range(13)]
rows={1<<i|1<<(j+13) for i in range(13) for j in range(13) if (i+j)%13 in D}
positives=sorted(rows)
neg=set()
for k in range(4):
 for g in combinations(range(13),k):
  p=sum(1<<i for i in g)
  l=8191
  for i in g: l &= ~N[i]
  neg.add(p|(l<<13)); neg.add(l|(p<<13))
neg={x for x in neg if not any(x!=y and x&y==x for y in neg)}
rows=positives+sorted(neg)
target=(1<<len(positives))-1
full=(1<<len(rows))-1
inputvals=[sum((r>>i&1)<<j for j,r in enumerate(rows)) for i in range(26)]
gates=[]
def gate(op,a,b):
 gates.append((op,a,b))
 return len(gates)+25
mode=int(sys.argv[1])
stars=[]
for i in range(13):
 ns=[13+j for j in range(13) if N[i]>>j&1]
 if mode&1:
  u=gate(1,ns[0],ns[1]); v=gate(1,u,ns[2]); w=gate(1,v,ns[3])
 else:
  u=gate(1,ns[0],ns[1]); v=gate(1,ns[2],ns[3]); w=gate(1,u,v)
 stars.append(gate(0,i,w))
while len(stars)>1:
 if mode&2:
  stars=[gate(1,stars[0],stars[1])]+stars[2:]
 else:
  stars=[gate(1,a,b) for a,b in zip(stars[::2],stars[1::2])]+(stars[-1:] if len(stars)%2 else [])
def compute(gs):
 vs=inputvals[:]
 for op,a,b in gs:
  vs.append(vs[a]|vs[b] if op else vs[a]&vs[b])
 return vs
assert compute(gates)[-1]==target
print('mode',mode,'gates',len(gates),'positive',len(positives),'maximal negative',len(neg),flush=True)
total=0
for k in range(64):
 for replacement in range(26+k):
  def remap(w):return replacement if w==26+k else w-(w>26+k)
  gs=[(op,remap(a),remap(b)) for j,(op,a,b) in enumerate(gates) if j!=k]
  output=remap(89)
  vs=compute(gs)
  def report(candidate):
   assert compute(candidate)[output]==target
   print('FOUND',k,replacement,flush=True)
   Path('.pnp/witness2056-'+str(mode)+'.json').write_text(json.dumps([candidate,output]))
   sys.exit(0)
  if vs[output]==target:report(gs)
  for j in range(63):
   if j+26>output:break
   def forced(value):
    z=vs[:26+j]+[value]
    for op,a,b in gs[j+1:output-25]:
     z.append(z[a]|z[b] if op else z[a]&z[b])
    return z[output]
   lo,hi=forced(0),forced(full)
   if lo&~target or target&~hi:continue
   obs=hi^lo
   need=target&obs
   total+=1
   for op in range(2):
    parents=[(a,x&obs) for a,x in enumerate(vs[:26+j]) if (x&obs&~need==0 if op else (need&~x)==0)]
    for ai,(a,x) in enumerate(parents):
     for b,y in parents[ai:]:
      if (x|y if op else x&y)==need:
       candidate=gs[:];candidate[j]=(op,a,b);report(candidate)
print('exhausted',mode,'repairable care masks',total,flush=True)
