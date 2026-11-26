"""Emit a lower_iso and lower_slice proof using a stored lower-bound certificate."""
from pathlib import Path
import json,re,sys
from cofactor_bounds import lookup,cache,folder

def move_list(pairs):
    loc=list(range(256))
    at=list(range(256))
    out=[]
    for src,dst in pairs:
        cur=loc[src]
        if cur==dst:continue
        displaced=at[dst]
        left,right=sorted((cur,dst))
        out.append(f'(1 <<< {left}, {right-left})')
        loc[src],loc[displaced]=dst,cur
        at[dst],at[cur]=src,displaced
    assert all(loc[i]==j for i,j in pairs)
    return '['+', '.join(out)+']'

def generate(table, candidate, aliases=()):
    bound,prior,file,key,order,pins=candidate
    data=(folder/file).read_text()
    m=re.search(rf'def dom_{key} : Nat := (0x[0-9a-fA-F]+)\s+def goal_{key} : Nat := (0x[0-9a-fA-F]+)\s+def roots_{key} : List Nat := \[([^\]]*)\]',data)
    source_dom=int(m[1],16)
    source_roots=[int(s.strip(),0) for s in m[3].split(',') if s.strip()]
    target_rows=[i for i in range(64) if all((i>>p)&1==v for p,v in pins.items()) and all(not ((i>>a ^ i>>b)&1) for a,b in aliases)]
    target_dom=sum(1<<r for r in target_rows)
    roots=[sum(1<<r for r in range(64) if r>>i&1) for i in range(6)]
    source_rows={sum(((w>>r)&1)<<j for j,w in enumerate(source_roots)):r for r in range(source_dom.bit_length()) if source_dom>>r&1}
    pairs=[(r,source_rows[sum(((r>>i)&1)<<j for j,i in enumerate(order))]) for r in target_rows]
    moves=move_list(pairs)
    witnesses=[]
    for i in pins:
        pair=next(((r,r^1<<i) for r in range(64) if (table>>r ^ table>>(r^1<<i))&1),None)
        if pair:witnesses.append(f'({hex(roots[i])}, {pair[0]}, {pair[1]})')
    ns=re.search(r'^namespace (PEqualNP\.Outside\.\w+_aux)\s*$',data,re.M)[1]
    def fmt(ns):return '['+', '.join(hex(n) for n in ns)+']'
    def ds(n):return ' '.join(['(by decide +kernel)']*n)
    print(f'-- Source {file}, restriction on {pins}, surviving inputs {order}.')
    print(f'open {ns}\n')
    print(f'def keptDomain : Nat := {hex(target_dom)}')
    print(f'def keptGoal : Nat := {hex(table&target_dom)}')
    print(f'def keptInputs : List Nat := {fmt([roots[i]&target_dom for i in order])}')
    print(f'theorem keptLower : Lower keptDomain keptInputs keptGoal {prior} :=')
    print(f'  lower_iso {moves} {ds(4)} low_{key}')
    print(f'theorem liftedLower : Lower {hex((1<<64)-1)} {fmt(roots)} {hex(table)} {bound} :=')
    print(f'  lower_slice {ds(7)}')
    print(f"    [{', '.join(witnesses)}] {ds(2)} keptLower")
if __name__=='__main__':
    t=int(sys.argv[1]); generate(t,lookup(t,json.loads(cache.read_text()))[0])
