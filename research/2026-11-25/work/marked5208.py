from functools import lru_cache
from pathlib import Path
import json
D={0,1,3,9}
g=[]
def gate(op,a,b):
    assert a!=b and max(a,b)<26+len(g)
    g.append((op,a,b));return 25+len(g)
star={}
for p in [1,0,*range(2,13)]:
    ns=[13+l for l in range(13) if (p-l)%13 in D]
    if p==0:ns[0]=gate(0,13,shared);first=ns[0]
    u=gate(1,*ns[:2]);v=gate(1,*ns[2:])
    if p==1:shared=u
    star[p]=gate(0,p,gate(1,u,v))
    if p==0:star[p]=gate(0,p,star[p]);last=star[p]
out=star[0]
for p in range(1,13):out=gate(1,out,star[p])
# Canonical reduced ordered BDD tests functional equality on every Boolean input.
nodes=[(26,0,0),(26,1,1)]; ids={}
def mk(i,l,r):
    if l==r:return l
    if (i,l,r) not in ids:
        ids[i,l,r]=len(nodes);nodes.append((i,l,r))
    return ids[i,l,r]
@lru_cache(None)
def apply(op,a,b):
    if a<2 and b<2:return a|b if op else a&b
    i=min(nodes[a][0],nodes[b][0])
    _,al,ar=nodes[a] if nodes[a][0]==i else (i,a,a)
    _,bl,br=nodes[b] if nodes[b][0]==i else (i,b,b)
    return mk(i,apply(op,al,bl),apply(op,ar,br))
inputs=[mk(i,0,1) for i in range(26)];vs=inputs[:]
for op,a,b in g:vs.append(apply(op,vs[a],vs[b]))
target=0
for p in range(13):
    for l in range(13):
        if (p-l)%13 in D:target=apply(1,target,apply(0,inputs[p],inputs[13+l]))
def evaluate(r):
    vals=[bool(r>>i&1) for i in range(26)]
    for op,a,b in g:vals.append(vals[a]|vals[b] if op else vals[a]&vals[b])
    return vals
def cone(w):
    if w<26:return set()
    _,a,b=g[w-26];return {a,b}|cone(a)|cone(b)
def check(k,s):
    op,a,b=g[k-26]
    return op==0 and k in cone(out)|{out} and evaluate(8193)[k] and not(evaluate(s)[a] or evaluate(s)[b])
assert len(g)==66 and vs[out]==target and first in cone(last)
assert check(first,1) and check(last,8192) and evaluate(8192)[first] and not evaluate(8192)[out]
print('66 gates, exact BDD equality; first gate',first-26,'second gate',last-26,'dirty input line 0 only')
Path('.pnp/marked5208.json').write_text(json.dumps([g,out,first,last]))
