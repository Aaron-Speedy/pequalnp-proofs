"""Search intersections of majorants from a single bypass in each star tree."""
from pathlib import Path
from itertools import combinations
import json, sys
setup = Path('.pnp/near2056.py').read_text().split('total=0')[0]
nodes = []
bygate = {}
values = []
costs = []
def node(op,a,b):
    if a==b:return a
    key=(op,min(a,b),max(a,b))
    if key not in bygate:
        ix=len(values); bygate[key]=ix
        values.append(values[a]|values[b] if op else values[a]&values[b])
        costs.append(costs[a]|costs[b]|(1<<(ix-26)))
        nodes.append(key)
    return bygate[key]
pool=set()
for mode in range(4):
    sys.argv=['major650',str(mode)]
    scope={}
    exec(setup,scope)
    gs=scope['gates']; target=scope['target']
    if not values:
        values.extend(scope['inputvals']); costs.extend([0]*26)
    for j in range(64):
        for sub in range(26+j):
            # Simulate first; intern only majorants that could contribute.
            vs=scope['inputvals'][:]
            for k,(op,a,b) in enumerate(gs):
                vs.append(vs[sub] if j==k else vs[a]|vs[b] if op else vs[a]&vs[b])
            if vs[-1]&target!=target:continue
            ids=list(range(26))
            for k,(op,a,b) in enumerate(gs):
                ids.append(ids[sub] if j==k else node(op,ids[a],ids[b]))
            pool.add(ids[-1])
print('distinct output nodes',len(pool),flush=True)
def save(a,b):
    seen={i:i for i in range(26)}; gates=[]
    def visit(i):
        if i not in seen:
            op,x,y=nodes[i-26]; x=visit(x);y=visit(y)
            gates.append((op,x,y));seen[i]=25+len(gates)
        return seen[i]
    out=visit(node(0,a,b))
    assert scope['compute'](gates)[out]==target
    if len(gates)<=63:
        Path('.pnp/major650-witness.json').write_text(json.dumps([gates,out]))
        print('candidate',len(gates),flush=True);sys.exit()
best=None;exact=0
for a,b in combinations(sorted(pool),2):
    if values[a]&values[b]!=target:continue
    exact+=1
    k=(costs[a]|costs[b]).bit_count()+1
    if best is None or k<best:
        best=k
        if k<=63:save(a,b)
print('exact intersections',exact,'best raw gate count',best,flush=True)
