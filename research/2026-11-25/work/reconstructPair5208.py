from ast import literal_eval
from itertools import combinations
from pathlib import Path
def test(kind):
    core=literal_eval(Path(f'.pnp/pairMarked5208-7-{kind}.log').read_text().splitlines()[1])
    g=[]
    def gate(op,a,b):g.append((op,a,b));return 8+len(g)
    ids=[0,1,gate(1,gate(1,2,3),4),gate(1,gate(1,5,6),7),8]
    for op,a,b in core:ids.append(gate(op,ids[a],ids[b]))
    selected=2 if kind==2 else 8;out=ids[-1]
    def sim(r):
        v=[bool(r>>i&1) for i in range(9)]
        for op,a,b in g:v.append(v[a]|v[b] if op else v[a]&v[b])
        return v
    cone=[set() for i in range(9)]
    for op,a,b in g:
        assert a!=b
        cone.append(cone[a]|cone[b]|{a,b})
    def ok(k,s):
        op,a,b=g[k];return not op and sim(1|1<<selected)[9+k] and not (sim(s)[a] or sim(s)[b])
    marks=next((i,j) for i,j in combinations(range(len(g)),2) if ok(i,1) and ok(j,1<<selected) and 9+i in cone[9+j] and (9+j in cone[out] or 9+j==out))
    badgate=None
    for r in range(512):
        val=sim(r);truth=bool((r&1 and r&284) or (r&2 and r&480))
        assert val[out]==truth
        if not truth:
            for k,(op,a,b) in enumerate(g):
                if not op and val[k+9]:badgate=k,r
    assert len(g)==11 and badgate
    print('marked line',selected,'gates',len(g),'checked rows',512,'marked gate indices',marks,'dirty witness',badgate)
test(2);test(4)
