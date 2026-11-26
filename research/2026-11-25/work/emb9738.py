from graph_restrict9750 import catalog
from pathlib import Path
import json,re
host=[0]*25
for i,j in json.load(open('.pnp/9738-edges.json')):host[i]|=1<<j;host[j]|=1<<i
def embed(n,E):
 a=[0]*n
 for i,j in E:a[i]|=1<<j;a[j]|=1<<i
 if any(not x or x.bit_count()>4 for x in a):return
 if any((x&y).bit_count()>1 for i,x in enumerate(a) for y in a[:i]):return
 def step(ans,domains):
  if len(ans)==n:return [ans[i] for i in range(n)]
  i=min((i for i in range(n) if i not in ans),key=lambda i:(domains[i].bit_count(),-a[i].bit_count()))
  ds=domains[i]
  while ds:
   bit=ds&-ds;ds^=bit;j=bit.bit_length()-1
   d=[v&~bit&(host[j] if a[i]>>k&1 else ~host[j]) for k,v in enumerate(domains)]
   val=step(ans|{i:j},d)
   if val:return val
 return step({},[sum(1<<j for j in range(25) if host[j].bit_count()>=v.bit_count()) for v in a])
def extra():
 for p in Path('lean/PEqualNP/Outside').glob('L_meta_97*.lean'):
  s=p.read_text().rsplit('theorem PEqualNP.Outside.',1)[-1].split(' := by',1)[0]
  m=re.search(r'¬ \(∃ C.*?Monotone2 C ∧ C.size ≤ (\d+) ∧ \(∀ x : Fin (\d+)',s)
  if m and int(m[2])<25:
   yield int(m[2]),{tuple(map(int,z)) for z in re.findall(r'\((\d+), (\d+)\)',s)},int(m[1])+1,str(p)
matches=[]
for n,E,k,f in [*extra(),*catalog()]:
 if k-n<3:continue
 mp=embed(n,E)
 if mp:matches.append((25-n+k,n,k,Path(f).stem,mp))
matches.sort(reverse=True)
print(matches[:8])
Path('.pnp/emb9738.json').write_text(json.dumps(matches))
