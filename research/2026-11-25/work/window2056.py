from functools import lru_cache
from itertools import combinations_with_replacement
from pathlib import Path
import sys,json
exec(Path('.pnp/near2056.py').read_text().split('total=0')[0])
s=int(sys.argv[2])
values=compute(gates)
def affected(root,bit):
    res=values[:]
    res[root]=bit
    for j in range(root+1,90):
        op,a,b=gates[j-26];res[j]=res[a]|res[b] if op else res[a]&res[b]
    return res[-1]
@lru_cache(None)
def windows(r,k):
    if k==0:return (frozenset(),)
    if r<26:return ()
    op,a,b=gates[r-26]
    return tuple({A|B|{r} for n in range(k) for A in windows(a,n) for B in windows(b,k-1-n)})
def run(root,W):
    unavailable=set(W)
    for wire,(op,a,b) in enumerate(gates,26):
        if a in unavailable or b in unavailable:unavailable.add(wire)
    lo,hi=affected(root,0),affected(root,full)
    care=lo^hi
    need=target&care; bad=care&~target
    atoms={v&care:i for i,v in enumerate(values) if i not in unavailable}
    pools=[atoms]
    for cost in range(1,(s-2)//2+1):
        pool={}
        for j in range((cost-1)//2+1):
            other=pools[cost-1-j]
            for a,ea in pools[j].items():
                for b,eb in other.items():
                    for op,val in ((0,a&b),(1,a|b)):
                        if val not in pool and all(val not in old for old in pools):
                            pool[val]=(op,ea,eb)
        pools.append(pool)
    @lru_cache(maxsize=60000)
    def solve(k,good,wrong):
        for a,ea in atoms.items():
            if (a&good)==good and not a&wrong:return ea
        if not k:return None
        for j in range((k-1)//2+1):
            for a,ea in pools[j].items():
                if a&good and not a&wrong:
                    eb=solve(k-1-j,good&~a,wrong)
                    if eb is not None:return (1,ea,eb)
                if a&good==good and wrong&~a:
                    eb=solve(k-1-j,good,wrong&a)
                    if eb is not None:return (0,ea,eb)
        return None
    expr=solve(s-1,need,bad)
    solve.cache_clear()
    if expr is None:return
    built=[];assigned={}
    def wire(i):
        if i<26:return i
        if i in assigned:return assigned[i]
        if i==root:ans=tree(expr)
        else:
            assert i not in W
            op,a,b=gates[i-26]
            ans=emit(op,wire(a),wire(b))
        assigned[i]=ans
        return ans
    def emit(op,a,b):
        built.append((op,a,b))
        return len(built)+25
    def tree(e):return wire(e) if isinstance(e,int) else emit(e[0],tree(e[1]),tree(e[2]))
    out=wire(89)
    assert len(built)<=63 and compute(built)[out]==target
    Path(f'.pnp/window-witness2056-{mode}-{s}.json').write_text(json.dumps([built,out]))
    print('Found',len(built),root,sorted(W),flush=True)
    sys.exit(0)
n=0
for root in range(26,90):
    for W in windows(root,s):
        run(root,W);n+=1
    if windows(root,s):
        print('root',root,'checked',n,flush=True)
print('exhausted',n,'windows of',s,'gates',flush=True)
