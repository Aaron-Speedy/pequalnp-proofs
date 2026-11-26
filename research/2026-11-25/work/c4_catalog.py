"""Grow connected graphs by nonisolated vertices; identify graphs up to relabeling."""
from itertools import combinations,permutations,product
from collections import defaultdict
from graph_gate_count import search
import sys,json,time

def canon(n,E):
    by_degree=defaultdict(list)
    for i in range(n):
        by_degree[sum(i in e for e in E)].append(i)
    parts=[list(permutations(v)) for _,v in sorted(by_degree.items())]
    best=None
    for groups in product(*parts):
        order=sum(groups,())
        mapping={old:new for new,old in enumerate(order)}
        code=tuple(sorted(tuple(sorted((mapping[i],mapping[j]))) for i,j in E))
        if best is None or code<best:best=code
    return best

def catalog(nmax):
    graphs=[()]
    yield 1,graphs
    for m in range(1,nmax):
        new=set()
        for E in graphs:
            adj=[set() for _ in range(m)]
            for i,j in E:adj[i].add(j);adj[j].add(i)
            for mask in range(1,1<<m):
                nb=[i for i in range(m) if mask>>i&1]
                if any(adj[i]&adj[j] for i,j in combinations(nb,2)):continue
                new.add(canon(m+1,list(E)+[(i,m) for i in nb]))
        graphs=sorted(new);yield m+1,graphs

if __name__=='__main__':
    from pathlib import Path
    out=Path('.pnp/graph-catalog-results.jsonl')
    prev={r['key'] for r in map(json.loads,out.read_text().splitlines())} if out.exists() else set()
    with out.open('a') as stream:
        for n,graphs in catalog(int(sys.argv[1])):
            if n<2:continue
            print('order',n,'classes',len(graphs),flush=True)
            for g in graphs:
                t=min(x.bit_count() for x in range(1<<n) if all((x>>i|x>>j)&1 for i,j in g))
                for kind,k in [('and',t-1),('or',len(g)-2)]:
                    key=str((n,g,kind,k))
                    if key in prev:continue
                    result='vacuous' if k<0 else search(n,g,kind,k,int(sys.argv[2]))
                    print(json.dumps(dict(key=key,n=n,g=g,kind=kind,k=k,result=result)),file=stream,flush=True)
                    if isinstance(result,list):print('witness',key,result,flush=True)
