import json,re,itertools
from pathlib import Path
d=Path('.pnp');source=Path('lean/PEqualNP/Outside/R_meta_4125_52.lean').read_text()
initial=json.loads(re.search(r'let initial := \((\[[0-9,]+\])',source)[1])
low=(1<<58)-1;want=(1<<21)-1
def evaluate(gs):
 v=initial[:]
 for op,a,b in gs:
    x,y=v[a],v[b]
    v.append(x|y if op else ((x&y&1729382256910270463)|(((x<<1)&y|x&(y<<1))&2882303761517117440)))
 return v
def seed(r,chain,reverse):
 gs=[]
 def gate(op,a,b):
    gs.append((op,a,b));return 13+len(gs)
 stars=[]
 for p in range(7):
    ns=[7+l for l in range(7) if (p-l)%7 in (0,1,3)]
    if reverse:ns.reverse()
    v=gate(1,gate(1,ns[0],ns[1]),ns[2])
    if p==r:miss=v
    else:stars.append(gate(0,p,v))
 while len(stars)>1:
    if chain:stars=[gate(1,stars[0],stars[1])]+stars[2:]
    else:stars=[gate(1,a,b) for a,b in zip(stars[::2],stars[1::2])]+(stars[-1:] if len(stars)%2 else [])
 h=stars[0];out=gate(0,gate(1,h,r),gate(1,h,miss));assert evaluate(gs)[out]==want
 return gs
def search(base):
 count=0
 for k in range(len(base)):
  w=14+k
  for new in range(w):
   def remap(x):return new if x==w else x-(x>w)
   gs=[(op,remap(a),remap(b)) for i,(op,a,b) in enumerate(base) if i!=k]
   out=remap(41);v=evaluate(gs)
   dup=[i for i,(_,a,b) in enumerate(gs) if a==b]
   if len(dup)>1:continue
   for j in (dup or range(len(gs))):
    if 14+j>out:continue
    def force(x):
        t=v[:14+j]+[x]
        for op,a,b in gs[j+1:out-13]:t.append(t[a]|t[b] if op else t[a]&t[b])
        return t[out]&low
    lo,hi=force(0),force(low)
    if lo&~want or want&~hi:continue
    care=lo^hi; need=want&care
    for op in range(2):
     pool=[(i,x&care) for i,x in enumerate(v[:14+j]) if ((x&care)&~need==0 if op else need&~x==0)]
     for (a,x),(b,y) in itertools.combinations(pool,2):
      if (x|y if op else x&y)!=need:continue
      alt=gs[:];alt[j]=(op,a,b);count+=1
      if evaluate(alt)[out]==want:
       assert all(a!=b and max(a,b)<14+i for i,(_,a,b) in enumerate(alt))
       d.joinpath('fano27-witness.json').write_text(json.dumps([alt,out]))
       print('found 27',flush=True);raise SystemExit
 return count
for r in (2,4,5,6):
 for chain,reverse in itertools.product(range(2),repeat=2):
    print(r,chain,reverse,search(seed(r,chain,reverse)),flush=True)
