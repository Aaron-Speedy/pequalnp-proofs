from pathlib import Path
import re,itertools,json
from functools import lru_cache
src=Path('lean/PEqualNP/Outside/R_meta_1969_744.lean').read_text()
chart=tuple(map(int,re.search(r'-- ([0-9]+ [0-9 ]+)[\n]-- ([0-9 ]+)[\n]-- ([0-9 ]+)[\n]-- ([0-9 ]+)',src).group(0).replace('--','').split()))
assert len(chart)==14
rows=[sum((n>>i&1)<<k for k,n in enumerate(chart)) for i in range(58)]
edges={tuple(k for k in range(14) if row>>k&1) for row in rows[:21]}
assert all(len(e)==2 and e[0]<7<=e[1] for e in edges) and len(edges)==21
certs=[]
for part in src.split('-- Input ')[1:]:
    header=part.splitlines()[0]; cap,seedcap,mass=map(int,re.search(r'Raw cap (\d+), seed cap (\d+), total mass (\d+)',header).groups())
    W=[[0]*37 for _ in range(21)]
    for i,cells in re.findall(r'^-- (\d+) \| ([^\n]+)',part.split('theorem PEqualNP')[0],re.M):
        for j,val in re.findall(r'(\d+)=(-?\d+)',cells):W[int(i)][int(j)]=int(val)
    assert sum(map(sum,W))==mass
    certs.append((cap,mass,W))
def score(sig,W):
    rr=[i for i in range(21) if sig>>i&1]
    cc=[j for j in range(37) if not (sig>>(j+21)&1)]
    if len(rr)>len(cc):arr=[[W[i][j] for i in rr] for j in cc]
    else:arr=[[W[i][j] for j in cc] for i in rr]
    if not arr:return 0
    cur=[0]*len(arr[0]);best=0;prev=0
    for h in range(1,1<<len(arr)):
        code=h^(h>>1);delta=code^prev;row=arr[delta.bit_length()-1]
        if code&delta:cur=[a+b for a,b in zip(cur,row)]
        else:cur=[a-b for a,b in zip(cur,row)]
        best=max(best,sum(v for v in cur if v>0));prev=code
    return best
for a,m,W in certs:assert max(score(v,W) for v in chart)==a
line=[frozenset(p for p in range(7) if (p,7+l) in edges) for l in range(7)]
dual=[frozenset(l for l in range(7) if (p,7+l) in edges) for p in range(7)]
group=[]
for perm in itertools.permutations(range(7)):
    moved=[frozenset(perm[i] for i in st) for st in line]
    if set(moved)==set(line):group.append(perm+tuple(7+line.index(s) for s in moved))
    if set(moved)==set(dual):group.append(tuple(7+i for i in perm)+tuple(dual.index(s) for s in moved))
assert len(group)==336
def repval(t,perm):
    if isinstance(t,int):return chart[perm[t]]
    op,x,y=t;x=repval(x,perm);y=repval(y,perm)
    return x|y if op else x&y
base=tuple(range(14))
one=[(op,i,j) for i,j in itertools.combinations(range(14),2) for op in range(2)]
two=[(op,t,i) for t in one for i in range(14) for op in range(2)]
def classify(family,k):
    found={};seen=set()
    for t in family:
        val=repval(t,base)
        if val in seen:continue
        orbit={repval(t,g):g for g in group};seen.update(orbit)
        witness=None
        for w,g in orbit.items():
            for i,(raw,mass,W) in enumerate(certs):
                cap=score(w,W)
                if (26-k)*raw+2*cap<mass:
                    witness=[i,cap,list(g),cap<=raw];break
            if witness:break
        found[str(t)]=[len(orbit),witness]
    return found
results={}
for k,fam in [(1,one),(2,two)]:
    part=classify(fam,k);results[k]=part
    print(k,'orbits',len(part),'excluded',sum(v[1] is not None for v in part.values()),'remaining',[(t,v[0]) for t,v in part.items() if v[1] is None],flush=True)
Path('.pnp/rect4126.json').write_text(json.dumps(results))
