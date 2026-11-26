from pathlib import Path
from itertools import combinations
from functools import lru_cache
import sys,json
data={}
exec(Path('.pnp/majorDouble650.py').read_text().split("print('distinct")[0],data)
double=data['pool'].copy()
single=Path('.pnp/major650.py').read_text()
exec(single[single.index('for mode in range(4)'):single.index("print('distinct")],data)
nodes,values,pool,target=[data[k] for k in ('nodes','values','pool','target')]
# Canonical n-ary AND/OR expressions. Absorb supersets by monotonicity.
def parts(op,e):return frozenset(e[1:]) if isinstance(e,tuple) and e[0]==op else frozenset([e])
@lru_cache(None)
def combine(op,terms):
    terms=frozenset().union(*(parts(op,x) for x in terms))
    sets={x:parts(1-op,x) for x in terms}
    terms=frozenset(x for x in terms if not any(s<sets[x] for s in sets.values()))
    if len(terms)==1:return next(iter(terms))
    return (op,*sorted(terms,key=repr))
@lru_cache(None)
def expr(i):
    if i<26:return i
    op,a,b=nodes[i-26]
    return combine(op,frozenset([expr(a),expr(b)]))
def meet(x,y):
    common=parts(1,x)&parts(1,y)
    if not common:return combine(0,frozenset([x,y]))
    a=parts(1,x)-common;b=parts(1,y)-common
    if not a or not b:return combine(1,common)
    return combine(1,common|{combine(0,frozenset([combine(1,a),combine(1,b)]))})
def build(e):
    gates=[];memo={}
    def wire(x):
        if isinstance(x,int):return x
        if x in memo:return memo[x]
        op=x[0]; args=[wire(v) for v in x[1:]]
        while len(args)>1:
            left,right=args.pop(),args.pop()
            key=(op,min(left,right),max(left,right),'gate')
            if key not in memo:
                memo[key]=26+len(gates);gates.append(key[:3])
            args.append(memo[key])
        memo[x]=args[0];return args[0]
    out=wire(e)
    return gates,out
pairs=0;transformed=set();best=1000
for a,b in combinations(sorted(pool),2):
    if values[a]&values[b]!=target:continue
    pairs+=1
    e=meet(expr(a),expr(b))
    if e in transformed:continue
    transformed.add(e)
    gates,out=build(e)
    assert data['scope']['compute'](gates)[out]==target
    best=min(best,len(gates))
    if len(gates)<=63:
        Path('.pnp/factor650-witness.json').write_text(json.dumps([gates,out]))
        break
print('pool',len(pool),'exact pairs',pairs,'distinct factorizations',len(transformed),'best',best,flush=True)
