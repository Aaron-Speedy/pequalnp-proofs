"""Identify checked unrestricted lower bounds that embed as induced subgraphs."""
from pathlib import Path
import re,subprocess,json
def edges(s):return {tuple(sorted(map(int,p))) for p in re.findall(r'x (\d+) && x (\d+)',s)}
def embed(n,E,m,H):
    neigh=lambda i,es:{v if u==i else u for u,v in es if i in (u,v)}
    A=[neigh(i,E) for i in range(n)]; B=[neigh(i,H) for i in range(m)]
    order=[]
    while len(order)<n:
        order.append(max(set(range(n))-set(order),key=lambda i:(len(A[i]&set(order)),len(A[i]))))
    def step(free,mp):
        if not free:return mp
        a,*rest=free
        for b in range(m):
            if b in mp.values() or len(B[b])<len(A[a]):continue
            if all((j in A[a])==(v in B[b]) for j,v in mp.items()):
                res=step(rest,mp|{a:b})
                if res:return res
    return step(order,{})
def catalog():
    files=subprocess.check_output(['rg','-l',r'^theorem PEqualNP\.Outside.*HasCircuitSize ([2-9]|1[012]) ', 'lean/PEqualNP/Outside'],text=True).splitlines()
    for f in files:
        s=Path(f).read_text().rsplit('theorem PEqualNP.Outside.',1)[-1].split(':=',1)[0]
        for m in re.finditer(r'∀ (\w+) : ℕ, PEqualNP\.MetaComplexity\.HasCircuitSize (\d+) \(fun (\w+) : Fin \2 → Bool => (.*?)\) \1 (?:→|↔) (\d+) ≤ \1\b',s):
            n=int(m[2]); var=m[3]; expr=m[4]
            if any(c in expr for c in ('∀','HasCircuitSize','→ Bool')):continue
            E={tuple(sorted(map(int,p))) for p in re.findall(rf'{var} (\d+) && {var} (\d+)',expr)}
            if not E and '.any' in expr:
                E={tuple(sorted(map(int,p))) for p in re.findall(r'\((\d+), (\d+)\)',expr)}
            if n<=12 and E: yield n,E,int(m[5]),f
if __name__=='__main__':
    H=edges(Path('lean/PEqualNP/Outside/L_meta_9750.lean').read_text()); matches=[]
    for n,E,L,f in catalog():
        mp=embed(n,E,12,H)
        if mp:matches.append((12-n+L,L,n,Path(f).name,[mp[i] for i in range(n)]))
    matches.sort(reverse=True)
    Path('.pnp/graph9750-embeds.json').write_text(json.dumps(matches))
    print(len(matches),matches[:7])
