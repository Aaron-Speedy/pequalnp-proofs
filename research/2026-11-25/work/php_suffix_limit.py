"""Enumerate only suffixes still compatible with a specified overall budget."""
import sys
from php_suffix import estimate,axioms,parents
budget=int(sys.argv[1])
limit=int(sys.argv[2])
states={frozenset([frozenset({(0,0)}),frozenset({(0,1)})])}
for depth in range(1,limit+1):
    if not states:
        print('no frontiers below budget at depth',depth,flush=True);break
    vals={K:depth+estimate(K) for K in states}
    live=[K for K,x in vals.items() if x<=budget]
    print('depth',depth,'minimum',min(vals.values()),'surviving',len(live),'of',len(states),flush=True)
    if depth==limit:break
    states=set()
    for K in live:
        cells={v for c in K for v,_ in c}
        rows={v//4 for v in cells};holes={v%4 for v in cells}
        freshrow=next((i for i in range(5) if i not in rows),None)
        freshhole=next((i for i in range(4) if i not in holes),None)
        for c in K:
            if c in axioms:continue
            other=K-{c}
            for v in range(20):
                if v//4 not in rows and v//4!=freshrow:continue
                if v%4 not in holes and v%4!=freshhole:continue
                if (v,0) in c or (v,1) in c:continue
                for a,b in parents(c,v):
                    candidate=other|{a,b}
                    if depth+1+estimate(candidate)<=budget:states.add(candidate)
                    if len(states)>15000:
                        print('stopped at frontier cap',depth+1,flush=True)
                        raise SystemExit
