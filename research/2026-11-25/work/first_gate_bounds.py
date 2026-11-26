"""Apply stored cofactor bounds after each possible first gate has been specified."""
import itertools,json,sys
from collections import Counter
from cofactor_bounds import lookup,cache

def analyse(t,idx):
    cols=[sum(1<<r for r in range(64) if r>>i&1) for i in range(6)]
    full=(1<<64)-1
    gates={('not',i,i):full^v for i,v in enumerate(cols)}
    for i,j in itertools.combinations(range(6),2):
        gates['and',i,j]=cols[i]&cols[j]
        gates['or',i,j]=cols[i]|cols[j]
    pairs=[[r for r in range(64) if (t>>r ^ t>>(r^(1<<i)))&1] for i in range(6)]
    cuts={}
    for cand in lookup(t,idx):
        pins=cand[5]
        key=tuple(sorted(pins.items()))
        if key in cuts: continue
        domain=full
        for p,v in key: domain &= cols[p] if v else full^cols[p]
        cuts[key]=domain,{0,domain}|{c&domain for c in cols},cand
    scores={}
    for gate,g in gates.items():
        distinguish={i for i,rs in enumerate(pairs) if any(not((g>>r ^ g>>(r^(1<<i)))&1) for r in rs)}
        options=[(cand[1]+1+len(distinguish.intersection(cand[5])),cand) for dom,avail,cand in cuts.values() if (g&dom) in avail]
        if options: scores[gate]=max(options,key=lambda o:o[0])
    return scores
if __name__=='__main__':
    idx=json.loads(cache.read_text())
    for t in map(int,sys.argv[1:]):
        scores=analyse(t,idx); count=Counter(n for n,c in scores.values())
        print(t,sorted(count.items()),'weakest first gates:',[g for g,(n,c) in scores.items() if n==min(count)])
