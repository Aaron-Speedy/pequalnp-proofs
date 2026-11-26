from pathlib import Path
from functools import reduce
from operator import and_
import json,subprocess
rows=[126,413,683,839,483,725,825,822,730,492]
def bits(w):return [i for i in range(10) if w>>i&1]
rect=set()
for mask in range(1,1024):
    cols=reduce(and_,[rows[i] for i in bits(mask)])
    if cols:rect.add((sum(1<<i for i,row in enumerate(rows) if row&cols==cols),cols))
rect=sorted(rect)
xs=[f'x{k}' for k in range(len(rect))]
lines=['min: '+' + '.join(xs)+';']
for i,r in enumerate(rows):
    for j in bits(r):
        lines.append(' + '.join(x for x,(a,b) in zip(xs,rect) if a>>i&1 and b>>j&1)+' >= 1;')
lines+=['bin '+', '.join(xs)+';']
d=Path('.pnp')
(d/'cover9294.lp').write_text('\n'.join(lines)+'\n')
p=subprocess.run(['lp_solve','-S2',str(d/'cover9294.lp')],text=True,capture_output=True,check=True)
chosen=[rect[int(k[1:])] for k,v in (line.split() for line in p.stdout.splitlines() if line.startswith('x')) if float(v)>0.5]
assert all(any(a>>i&1 and b>>j&1 for a,b in chosen)==bool(r>>j&1) for i,r in enumerate(rows) for j in range(10))
print('maximal rectangles',len(rect),'optimum',len(chosen),chosen)
(d/'cover9294.json').write_text(json.dumps(chosen))
