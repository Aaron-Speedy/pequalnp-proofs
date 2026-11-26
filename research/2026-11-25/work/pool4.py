from short4 import best,resolve
from itertools import permutations
from pathlib import Path
import json,sys
allm=[]
for p in permutations(range(4)):
 for q in permutations(range(3)):
  mp=[3*p[i//3]+q[i%3] for i in range(12)]
  def transform(c):
    return sum(1<<(mp[i]+s) for i in range(12) for s in (0,20) if c>>(i+s)&1)
  allm.append({transform(c):tuple([transform(h[0]),transform(h[1]),mp[h[2]]]) if h else None for c,h in best.items()})
allm.sort(key=lambda g:-len(set(g)&set(best)))
lim=int(sys.argv[1]);gs=allm[:lim]
depth={}
for g in gs:
 d={}
 for c,h in g.items():
  d[c]=0 if not h else 1+max(d[h[0]],d[h[1]])
  depth[c]=min(depth.get(c,1000),d[c])
ids={c:i+1 for i,c in enumerate(sorted(depth,key=lambda c:(depth[c],c)))};cs=list(ids)
opts={c:[] for c in cs}
for j,b in enumerate(cs):
 for a in cs[:j]:
  pair=resolve(a,b)
  if pair:
   c,h=pair
   if c in ids and max(ids[a],ids[b])<ids[c]: opts[c].append(h)
ax=[c for c in cs if depth[c]==0]
form=[[ids[c]] for c in ax]+[[ids[0]]];n=len(cs);supp={}
for c in cs:
 if c in ax:continue
 row=[-ids[c]]
 for a,b,k in opts[c]:
  n+=1;row.append(n);supp[n]=[c,a,b,k];form.extend([[-n,ids[a]],[-n,ids[b]]])
 form.append(row)
# Forward-only sequential unary count, forbidding a 34th selected derived line.
prev=[];max_derived=55-len(ax)
for c in cs:
 if c in ax:continue
 v=ids[c];curr=[]
 for j in range(min(len(prev)+1,max_derived+1)):
  n+=1;curr.append(n)
  if j<len(prev):form.append([-prev[j],n])
  form.append(([-v,n] if j==0 else [-v,-prev[j-1],n]))
 if len(curr)>max_derived:form.append([-curr[-1]])
 prev=curr
path=Path('.pnp/pool4-'+str(lim))
with path.with_suffix('.cnf').open('w') as out:
 print('p cnf',n,len(form),file=out)
 for cl in form:print(*cl,0,file=out)
path.with_suffix('.json').write_text(json.dumps([ax,supp]))
print(lim,len(cs),n,len(form),flush=True)
