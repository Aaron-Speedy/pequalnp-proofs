from pathlib import Path
import ast
import itertools
import json
d=Path('.pnp')
ns={}
exec((d/'rect4126.py').read_text().split('results={}')[0],ns)
sigs=ns['chart']; rows=ns['rows']; edges=ns['edges']
def incident(x):
    return any(x&(1<<i) and x&(1<<j) for i,j in edges)
def maximal(x):
    return not incident(x) and all(incident(x|1<<i) for i in range(14) if not x&(1<<i))
assert set(rows[21:])=={x for x in range(1<<14) if maximal(x)}
matrices=list(ns['certs'])
for k in range(2):
    obj=json.loads((d/f'customRect4126-{k}.json').read_text())
    matrices.append((obj['cap'],obj['mass'],obj['matrix']))
def capacity(word,matrix):
    rr=[i for i in range(21) if word>>i&1]
    cc=[j for j in range(37) if not word>>(21+j)&1]
    m=[[matrix[i][j] for j in cc] for i in rr]
    if len(cc)<len(rr):m=list(zip(*m))
    best=0
    for k in range(1,len(m)+1):
        for subset in itertools.combinations(m,k):
            best=max(best,sum(max(sum(col),0) for col in zip(*subset)))
    return best
for raw,total,m in matrices:
    assert sum(map(sum,m))==total
    assert max(capacity(s,m) for s in sigs)==raw
result=json.loads((d/'allRead4126.json').read_text())
for k,family in [(1,ns['one']),(2,ns['two'])]:
    covered=set()
    for expr,(size,(idx,claimed,perm,_)) in result[str(k)].items():
        t=ast.literal_eval(expr)
        orbit={ns['repval'](t,g) for g in ns['group']}
        assert not (orbit&covered) and len(orbit)==size
        covered.update(orbit)
        assert tuple(perm) in ns['group']
        raw,total,m=matrices[idx]
        cap=capacity(ns['repval'](t,perm),m)
        assert cap==claimed and cap<=raw and total>(26-k)*raw+2*cap
    assert covered=={ns['repval'](t,ns['base']) for t in family}
    print(k,len(result[str(k)]),len(covered),'all verified')
