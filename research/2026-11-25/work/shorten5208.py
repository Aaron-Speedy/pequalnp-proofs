from marked5208 import g,out,target,inputs,apply
from itertools import combinations
from pathlib import Path
import json
base=len(g)
def trial(deletes):
    ids=list(range(26)); gs=[]; mini=[1 if i==0 else 2 if i==13 else 0 for i in range(26)]
    # bits 0,1,2 represent point singleton, line singleton, and the pair.
    mini[0]=5;mini[13]=6
    below=[0]*26;left=right=dirty=0
    for i,(op,a,b) in enumerate(g):
        if i in deletes:
            ids.append(ids[deletes[i]]);continue
        a,b=ids[a],ids[b]
        if a==b:return
        own=1<<len(gs);cones=below[a]|below[b];v=mini[a]|mini[b] if op else mini[a]&mini[b]
        if not op:
            if v&4:
                if not ((mini[a]|mini[b])&1):left|=own
                if not ((mini[a]|mini[b])&2) and cones&left:right|=own
            if v&3:dirty|=own
        ids.append(26+len(gs));gs.append((op,a,b));mini.append(v);below.append(cones|own)
    w=ids[out]
    if not right&below[w] or not dirty:return
    vs=inputs[:]
    for op,a,b in gs:vs.append(apply(op,vs[a],vs[b]))
    if vs[w]==target:
        print('candidate',len(gs),deletes,flush=True)
        Path(f'.pnp/marked5208-{len(gs)}.json').write_text(json.dumps([gs,w]))
        return True
for j in range(base):
    for sub in range(26+j):
        if trial({j:sub}):break
    else:continue
    break
else:print('single substitutions exhausted',flush=True)
for i,j in combinations(range(base),2):
    for a in g[i][1:]:
        for b in range(26+j):
            if trial({i:a,j:b}):raise SystemExit
print('two substitutions exhausted with a singleton dirtiness witness',flush=True)
