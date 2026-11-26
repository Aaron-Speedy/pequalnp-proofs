"""Check every emitted CNF clause on the repository's explicit resolution DAG."""
from pathlib import Path
import re
import sys
import tempfile
from php_bound import axiom_rows, encode

def cert():
    text=Path('lean/PEqualNP/Outside/L_pcx_171.lean').read_text().split('def cert :')[1].split('theorem hc')[0]
    graph={}
    lines=[]
    for line in reversed([l for l in text.splitlines() if l.strip().startswith('(')]):
        c=frozenset((int(a)*4+int(b),int(s=='false')) for a,b,s in re.findall(r'\(\((\d+), (\d+)\), (true|false)\)',line))
        h=re.search(r'some \((\d+), (\d+), \((\d+), (\d+)\)\)',line)
        edge=None
        if h:
            i,j,p,k=map(int,h.groups())
            edge=(lines[-1-i],lines[-1-j],p*4+k)
        graph[c]=edge;lines.append(c)
    return graph

def model():
    graph=cert()
    forms=list(map(frozenset,axiom_rows(4)))
    ids={c:i for i,c in enumerate(forms)}
    edges=[]
    while len(forms)<len(graph):
        possible=((max(ids[a],ids[b]),ids[a],ids[b],v,c) for c,h in graph.items()
                  if c not in ids and h for a,b,v in [h] if a in ids and b in ids)
        _,a,b,v,c=min(possible)
        assert (forms[a]-{(v,0)}) | (forms[b]-{(v,1)}) == c
        ids[c]=len(forms);forms.append(c);edges.append((a,b,v))
    assert edges[0]==(0,5,0) and not forms[-1]
    bits=[False]
    def vals(c):
        return [(v,sign) in c for v in range(20) for sign in range(2)]
    def choice(n,k):
        bits.extend(j==k for j in range(n))
        bits.extend(j>=k for j in range(1,n))
    for c in forms: bits.extend(vals(c))
    for i,(a,b,v) in enumerate(edges,45):
        choice(20,v)
        for src in (a,b):
            choice(i,src);bits.extend(vals(forms[src]))
    return bits,len(forms)

if __name__=='__main__':
    bits,n=model()
    with tempfile.TemporaryDirectory(dir='.pnp') as tmp:
        path=Path(tmp)/'php157.cnf'
        encode(4,n,path)
        with path.open() as f:
            _,_,num_vars,num_clauses=next(f).split()
            assert int(num_vars)==len(bits)-1
            for i,line in enumerate(f,1):
                c=map(int,line.split()[:-1])
                assert any(bits[abs(v)]==(v>0) for v in c), i
            assert i==int(num_clauses)
    print(f'Known {n}-line derivation satisfied all {i} clauses.')
