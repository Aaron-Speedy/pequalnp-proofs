from pathlib import Path
from itertools import combinations
from functools import lru_cache
import sys,json
scope={}
sys.argv=['mixed650','0']
exec(Path('.pnp/near2056.py').read_text().split('total=0')[0],scope)
target=scope['target']; inputs=scope['inputvals']; N=scope['N']
nodes=[]; ids={}; values=inputs[:]
def node(op,a,b):
    if a==b:return a
    key=(op,min(a,b),max(a,b))
    if key not in ids:
        ids[key]=len(values);nodes.append(key)
        values.append(values[a]|values[b] if op else values[a]&values[b])
    return ids[key]
exec('def parts'+Path('.pnp/factor650.py').read_text().split('def parts',1)[1].split('pairs=0')[0])
def seed(k,mode):
    gates=[]
    def new(op,a,b):
        gates.append((op,a,b));return len(gates)+25
    def either(ws,chain):
        while len(ws)>1:
            if chain:ws=[new(1,ws[0],ws[1])]+ws[2:]
            else:ws=[new(1,a,b) for a,b in zip(ws[::2],ws[1::2])]+(ws[-1:] if len(ws)%2 else [])
        return ws[0]
    moved=[p for p,n in enumerate(N) if n&1][:k]
    stars=[]
    for p,n in enumerate(N):
        cols=[13+l for l in range(13) if n>>l&1 and (l or p not in moved)]
        stars.append(new(0,p,either(cols,mode&1)))
    if moved:stars.append(new(0,13,either(moved,mode&1)))
    out=either(stars,mode&2)
    assert scope['compute'](gates)[out]==target
    return gates
# Deduplicate by normalized expression, then by evaluation to find compatible pairs.
families={}
for k in (0,2,3,4):
 for mode in range(4):
    gs=seed(k,mode)
    for skip in range(len(gs)):
     for sub in range(26+skip):
        vs=inputs[:]
        for i,(op,a,b) in enumerate(gs):
            vs.append(vs[sub] if i==skip else vs[a]|vs[b] if op else vs[a]&vs[b])
        if vs[-1]&target!=target:continue
        ids_here=list(range(26))
        for i,(op,a,b) in enumerate(gs):
            ids_here.append(ids_here[sub] if i==skip else node(op,ids_here[a],ids_here[b]))
        families.setdefault(vs[-1],set()).add(expr(ids_here[-1]))
best=999; tested=set(); exact=0
for i,(v,es) in enumerate(families.items()):
 for w,fs in list(families.items())[i:]:
    if v&w!=target:continue
    for e in es:
     for f in fs:
        exact+=1;x=meet(e,f)
        if x in tested:continue
        tested.add(x);gs,out=build(x)
        assert scope['compute'](gs)[out]==target
        best=min(best,len(gs))
        if len(gs)<=63:
            Path('.pnp/mixed650-witness.json').write_text(json.dumps([gs,out]))
            print('candidate',len(gs),flush=True);sys.exit(0)
print('majorant signatures',len(families),'exact expression pairs',exact,'distinct factorizations',len(tested),'best',best)
