"""Exhaust small OR-gate budgets by enumerating intersections of existing wires."""
from itertools import combinations
from functools import lru_cache
import time

class Cutoff(Exception): pass

def solve(n,edge_pairs,kind,budget,seconds=15):
    edges=[1<<i|1<<j for i,j in edge_pairs]
    istrue=lambda r:any(r&e==e for e in edges)
    false=[r for r in range(1<<n) if not istrue(r) and all(istrue(r|1<<i) for i in range(n) if not r>>i&1)]
    rows=edges+false;allrows=(1<<len(rows))-1
    target=(1<<len(edges))-1
    if kind=='and':
        rows=[((1<<n)-1)^r for r in rows]
        target^=allrows
    def extend(closed,w):
        return closed|frozenset(old&w for old in closed)
    bank=frozenset([allrows])
    for i in range(n):
        bank=extend(bank,sum(1<<r for r,x in enumerate(rows) if x>>i&1))
    def hull(closed, need):
        bitmask=allrows
        for wire in closed:
            if need & ~wire == 0:bitmask &= wire
        return bitmask
    visited=0;deadline=time.monotonic()+seconds
    @lru_cache(maxsize=4096)
    def rec(closed,rem):
        nonlocal visited
        visited+=1
        if time.monotonic()>deadline:raise Cutoff
        if target in closed:return True
        if rem==0:return False
        if rem==1:
            outside=hull(closed,target)&~target
            # For every partition, its two minimal covering meets are the
            # strongest branches. Swapping branches gives the same final OR.
            sub=target
            while sub:
                complement=target^sub
                if sub<complement:break
                if not ((hull(closed,sub)|hull(closed,complement))&outside):return True
                sub=(sub-1)&target
            return False
        candidates={a|b for a,b in combinations(closed,2)}-closed
        return any(rec(extend(closed,w),rem-1) for w in sorted(candidates,key=lambda w:(w^target).bit_count()))
    try:res=rec(bank,budget)
    except Cutoff:res=None
    return res,visited

if __name__=='__main__':
    for n in [3,5,6]:
        edges=[(i,(i+1)%n) for i in range(n)]
        for kind,k in [('or',n-2),('and',(n+1)//2-1)]:
            for budget in [k,k+1]:
                print(n,kind,budget,solve(n,edges,kind,budget,8),flush=True)
