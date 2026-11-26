"""Lower-bound a short resolution suffix by the simultaneous prefix obligations."""
from functools import lru_cache
from itertools import combinations,product
from php_rank import critical_masks,rank
from php_bound import axiom_rows
import sys
masks,banks,all_cases=critical_masks(4)
axioms=[frozenset(c) for c in axiom_rows(4)]
@lru_cache(None)
def obligations(c):
    if c in axioms[5:]:return 0,0
    common=all_cases
    for l in c:common&=masks[l]
    used=0;covered=0
    for j in range(5,45):
        if common & banks[j]:
            k=j-5;used|=1<<k
            if not c & axioms[j]:covered|=1<<k
    return used,covered
edges=list(combinations(range(5),2))
vertex=[min(s.bit_count() for s in range(32) if all(not (g>>i&1) or ((s>>a|s>>b)&1) for i,(a,b) in enumerate(edges))) for g in range(1024)]
@lru_cache(None)
def cover(g):
    return sum(vertex[sum(((g>>(e*4+h))&1)<<e for e in range(10))] for h in range(4))

def estimate(K):
    used=hits=0
    for c in K:
        a,b=obligations(c);used|=a;hits|=b
    return 45+used.bit_count()+cover(hits)

def parents(c,v):
    lits=tuple(c)
    for choices in product((1,2,3),repeat=len(lits)):
        yield (frozenset({(v,0)}|{l for l,p in zip(lits,choices) if p&1}),
               frozenset({(v,1)}|{l for l,p in zip(lits,choices) if p&2}))
def run(maxdepth):
    states={frozenset([frozenset({(0,0)}),frozenset({(0,1)})])}
    for depth in range(1,maxdepth+1):
        print('inferences peeled:',depth,'min overall bound',depth+min(map(estimate,states)),'frontiers',len(states),flush=True)
        if depth==maxdepth:break
        expanded=set()
        for K in states:
            for c in K:
                if c in axioms:continue
                other=K-{c}
                for v in range(20):
                    if (v,0) in c or (v,1) in c:continue
                    for a,b in parents(c,v):expanded.add(other|{a,b})
        states=expanded
if __name__=='__main__':run(int(sys.argv[1]))
