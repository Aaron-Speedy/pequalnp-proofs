"""Locate checked circuit lower bounds on coordinate restrictions of a six-input table."""
import itertools
import json
from pathlib import Path
import re
import subprocess
import sys

folder = Path('lean/PEqualNP/Outside')
cache = Path('.pnp/cofactor-index.json')
def read_index():
    result = {}
    files = subprocess.check_output(['rg','-l','theorem low_[0-9]+ : Lower dom_',str(folder)],text=True).splitlines()
    for filename in sorted(files):
        data = Path(filename).read_text()
        for key,lower in re.findall(r'theorem low_(\d+) : Lower dom_\1 roots_\1 goal_\1 (\d+)\b',data):
            block = re.search(rf'def dom_{key} : Nat := (0x[\da-fA-F]+)\s+def goal_{key} : Nat := (0x[\da-fA-F]+)\s+def roots_{key} : List Nat := \[([^\]]*)\]',data)
            if not block: continue
            dm,goal = [int(block[i],16) for i in (1,2)]
            if not re.fullmatch(r'[0-9a-fA-Fx,\s]*',block[3]):continue
            roots = [int(v,0) for v in block[3].split(',') if v.strip()]
            if len(roots)>6 or dm.bit_count() != 1<<len(roots): continue
            rows = [r for r in range(dm.bit_length()) if (dm>>r)&1]
            order = [sum(((v>>r)&1)<<i for i,v in enumerate(roots)) for r in rows]
            if len(set(order))!=len(order):continue
            table=sum(((goal>>r)&1)<<i for r,i in zip(rows,order))
            idx=f'{len(roots)},{table}'
            record=[int(lower),Path(filename).name,key]
            if idx not in result or result[idx][0] < record[0]:result[idx]=record
    cache.write_text(json.dumps(result))
    return result

def lookup(table,index):
    essential={i for i in range(6) if any((table>>r ^ table>>(r^(1<<i)))&1 for r in range(64))}
    found=[]
    for arity in range(3,7):
        for keep in itertools.combinations(range(6),arity):
            if not set(keep)<=essential:continue
            pins=sorted(set(range(6))-set(keep))
            for order in itertools.permutations(keep):
                base_rows=[sum(((r>>i)&1)<<j for i,j in enumerate(order)) for r in range(1<<arity)]
                for values in itertools.product(range(2),repeat=len(pins)):
                    setbits=sum(v<<i for v,i in zip(values,pins))
                    co=sum(((table>>(setbits|r))&1)<<k for k,r in enumerate(base_rows))
                    rec=index.get(f'{arity},{co}')
                    if rec:
                        bound,name,key=rec
                        found.append((bound+len(essential-set(keep)),bound,name,key,order,dict(zip(pins,values))))
    return sorted(found,key=lambda f:(-f[0],f[1],f[2]))
if __name__=='__main__':
    index=read_index() if not cache.exists() else json.loads(cache.read_text())
    print('checked-source tables indexed:',len(index))
    for arg in sys.argv[1:]:
        candidates=lookup(int(arg),index)
        print(arg,candidates[0] if candidates else None)
