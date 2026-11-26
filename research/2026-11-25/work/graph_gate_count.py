"""Test a one-gate-type budget for monotone graph functions on extremal assignments."""
import itertools,json,subprocess,tempfile
from pathlib import Path
solver=Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
class Formula:
    def __init__(self):self.n=0;self.clauses=[]
    def var(self):
        self.n+=1;return self.n
    def add(self,*xs): self.clauses.append(xs)
    def conjunction(self,lits):
        r=self.var()
        for a in lits:self.add(-r,a)
        self.add(r,*[-x for x in lits]);return r

def search(n,edges,kind,k,timeout):
    edges=tuple((1<<i)|(1<<j) for i,j in edges)
    f=lambda x:any(x&e==e for e in edges)
    false=[r for r in range(1<<n) if not f(r) and all(f(r|1<<i) for i in range(n) if not r>>i&1)]
    rows=list(edges)+false
    # Dualizing lets the same formula count ORs on f or ORs on its dual.
    if kind=='and':
        rows=[((1<<n)-1)^r for r in rows]
        targets=[False]*len(edges)+[True]*len(false)
    else:targets=[True]*len(edges)+[False]*len(false)
    cnf=Formula();one=cnf.var();cnf.add(one)
    bank=[[one if r>>i&1 else -one for r in rows] for i in range(n)]
    sels=[]
    def side():
        sel=[cnf.var() for _ in bank]
        vals=[]
        for j in range(len(rows)):
            lits=[]
            for s,w in zip(sel,bank):
                u=w[j]
                if u==one:continue
                if u==-one:lits.append(-s)
                else:lits.append(-cnf.conjunction([s,-u]))
            vals.append(cnf.conjunction(lits))
        sels.append(sel)
        return vals
    for _ in range(k):
        a=side();b=side()
        bank.append([-cnf.conjunction([-x,-y]) for x,y in zip(a,b)])
    output=side()
    for v,y in zip(output,targets):cnf.add(v if y else -v)
    with tempfile.NamedTemporaryFile(mode='w') as file:
        print('p cnf',cnf.n,len(cnf.clauses),file=file)
        for clause in cnf.clauses:print(*clause,0,file=file)
        file.flush()
        p=subprocess.run([solver,'-q','-t',str(timeout),file.name],capture_output=True,text=True)
    if p.returncode==20:return 'unsat'
    if p.returncode==0:return 'timeout'
    if p.returncode!=10:raise RuntimeError(p.stderr)
    m={int(x) for l in p.stdout.splitlines() if l.startswith('v ') for x in l.split()[1:]}
    reads=[[i for i,s in enumerate(sel) if s in m] for sel in sels]
    for r in range(1<<n):
        x=[(bool(r>>i&1) if kind=='or' else not bool(r>>i&1)) for i in range(n)]
        for a,b in zip(reads[:-1:2],reads[1:-1:2]):
            x.append(all(x[i] for i in a) or all(x[i] for i in b))
        y=all(x[i] for i in reads[-1])
        assert (y if kind=='or' else not y)==f(r)
    return reads

if __name__=='__main__':
    graphs={'triangle':(3,[(0,1),(1,2),(2,0)]),'five_cycle':(5,[(i,(i+1)%5) for i in range(5)]),'two_triangles':(5,[(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]),'six_cycle':(6,[(i,(i+1)%6) for i in range(6)]),'seven_cycle':(7,[(i,(i+1)%7) for i in range(7)])}
    for name,(n,e) in graphs.items():
        cover=min(r.bit_count() for r in range(1<<n) if all((r>>i|r>>j)&1 for i,j in e))
        for kind,k in [('and',cover-1),('or',len(e)-2)]:
            res=search(n,e,kind,k,30)
            print(name,kind,k,json.dumps(res),flush=True)
