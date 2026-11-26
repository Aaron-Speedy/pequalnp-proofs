"""Allow duplicated variables when restricting a circuit to a smaller truth table."""
import itertools
import json
import sys
from cofactor_bounds import cache

def bounds(tables,index):
    best={t:None for t in tables}
    for k in (3,4,5):
        all_blocks=set(range(k))
        choices=list(range(k))+['zero','one']
        for assign in itertools.product(choices,repeat=6):
            if sum(isinstance(a,int) for a in assign)<=k or not all_blocks.issubset(assign):continue
            pins=[i for i,a in enumerate(assign) if isinstance(a,str)]
            base=sum(1<<i for i,a in enumerate(assign) if a=='one')
            blocks=[sum(1<<i for i,a in enumerate(assign) if a==j) for j in range(k)]
            rows=[base]
            for b in blocks:rows += [r|b for r in rows]
            for t in tables:
                small=sum(((t>>r)&1)<<j for j,r in enumerate(rows))
                if record:=index.get(f'{k},{small}'):
                    saved=sum(any((t>>r^t>>(r^(1<<i)))&1 for r in range(64)) for i in pins)
                    bound=record[0]+saved
                    if best[t] is None or best[t][0]<bound:best[t]=(bound,record,assign)
    return best
if __name__=='__main__':
    for t,rec in bounds([int(x) for x in sys.argv[1:]],json.loads(cache.read_text())).items(): print(t,rec)
