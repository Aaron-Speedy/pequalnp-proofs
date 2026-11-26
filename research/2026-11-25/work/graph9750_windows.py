"""Search for single-output replacements inside 21-gate star circuits on their care rows."""
import itertools,json,random
from functools import lru_cache
from pathlib import Path
from graph_restrict9750 import edges
G=edges(Path('lean/PEqualNP/Outside/L_meta_9750.lean').read_text())
cols=[sum(1<<r for r in range(4096) if r>>i&1) for i in range(12)]
allrows=(1<<4096)-1
target=0
for i,j in G:target |= cols[i]&cols[j]
def eval_gate(op,a,b):return a&b if op=='and' else a|b if op=='or' else allrows^a
def run(gs,override=None):
    w=cols.copy()
    for op,i,j in gs:
        idx=len(w)
        w.append(override[1] if override is not None and override[0]==idx else eval_gate(op,w[i],w[j]))
    return w
def star(rng,side):
    gs=[]
    def combine(op,x,y):
        gs.append((op,x,y));return len(gs)+11
    def merge(v):
        v=list(v)
        while len(v)>1:
            rng.shuffle(v);v.append(combine('or',v.pop(),v.pop()))
        return v[0]
    outs=[]
    for i in rng.sample(list(range(6*side,6*side+6)),6):
        outs.append(combine('and',i,merge([j if i==k else k for k,j in G if i in (k,j)])))
    merge(outs)
    assert run(gs)[-1]==target
    return gs
@lru_cache(None)
def solve(inputs,goal,mask,k):
    if goal in inputs:return []
    if k==0:return None
    candidate={}
    for i,a in enumerate(inputs):
        candidate.setdefault(a^mask,('not',i,i))
        for j,b in enumerate(inputs[:i]):
            candidate.setdefault(a&b,('and',i,j));candidate.setdefault(a|b,('or',i,j))
    if goal in candidate:return [candidate[goal]]
    if k==1:return None
    for v,g in candidate.items():
        if v in inputs:continue
        # An actual circuit may use a generated constant as well.
        tail=solve(inputs+(v,),goal,mask,k-1)
        if tail is not None:return [g]+tail
    return None
def trial(gs):
    w=run(gs); users=[set() for _ in w]
    for t,(_,a,b) in enumerate(gs,12):
        users[a].add(t);users[b].add(t)
    checked=0
    for out in range(12,len(w)):
        for depth in (2,3,4):
            stack=[frozenset([out])]; seen=set(stack)
            while stack:
                block=stack.pop()
                frontier=sorted({z for t in block for z in gs[t-12][1:] if z not in block})
                if len(block)<depth:
                    for z in frontier:
                        if z<12 or not users[z]<=block:continue
                        b=block|{z}
                        if b not in seen:seen.add(b);stack.append(b)
                    continue
                cm=run(gs,(out,0))[-1]^run(gs,(out,allrows))[-1]
                patterns={}
                for r in range(4096):
                    if not(cm>>r&1):continue
                    key=sum(((w[z]>>r)&1)<<k for k,z in enumerate(frontier));v=w[out]>>r&1
                    assert patterns.setdefault(key,v)==v
                rows=sorted(patterns)
                inputs=tuple(sum(((row>>i)&1)<<p for p,row in enumerate(rows)) for i in range(len(frontier)))
                goal=sum(patterns[row]<<p for p,row in enumerate(rows))
                answer=solve(inputs,goal,(1<<len(rows))-1,depth-1)
                checked+=1
                if answer is not None:
                    return checked,(gs,sorted(block),frontier,out,answer)
    return checked,None
if __name__=='__main__':
    rng=random.Random(9750)
    count=0
    for ix in range(120):
        gs=star(rng,ix%2); k,a=trial(gs);count+=k
        if a:
            print('witness',json.dumps(a));break
        if ix%10==9:print(ix+1,count,flush=True)
        solve.cache_clear()
