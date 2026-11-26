"""Expand RUP chains to binary resolution and count distinct ancestors of bottom."""
import itertools
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

solver = Path.home() / '.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
def php():
    rows = [[4*i+j+1 for j in range(4)] for i in range(5)]
    return rows + [[-a[j], -b[j]] for a,b in itertools.combinations(rows,2) for j in range(4)]

def search(seed, work):
    rng = random.Random(seed)
    axioms = php()
    names = list(range(1,21))
    rng.shuffle(names)
    forward = {i+1:r for i,r in enumerate(names)}
    inverse = {r:i for i,r in forward.items()}
    def rename(v, m):
        return m[abs(v)] * (1 if v > 0 else -1)
    rng.shuffle(axioms)
    clauses = {}
    graph = {}
    cnf = work / 'in.cnf'
    trace = work / 'out.lrat'
    with cnf.open('w') as stream:
        print('p cnf 20 45',file=stream)
        for i,clause in enumerate(axioms,1):
            rng.shuffle(clause)
            print(*(rename(v,forward) for v in clause),0,file=stream)
            clauses[i] = frozenset(clause)
            graph[clauses[i]] = None
    result = subprocess.run([solver,'-q','--plain','--lrat','--no-binary',cnf,trace],capture_output=True)
    if result.returncode != 20: raise RuntimeError(result.stderr)
    for line in trace.read_text().splitlines():
        items = line.split()
        if items[1]=='d': continue
        code = list(map(int,items))
        split = code.index(0)
        desired = frozenset(rename(v,inverse) for v in code[1:split])
        hints = code[split+1:-1]
        assigned = {-v for v in desired}
        trail = []
        for hint in hints:
            c = clauses[hint]
            if c & assigned: continue
            fresh = [v for v in c if -v not in assigned]
            if not fresh:
                out = c
                break
            if len(fresh)!=1: raise ValueError('nonunit LRAT hint')
            pivot, = fresh
            trail.append((pivot,c))
            assigned.add(pivot)
        else: raise ValueError('missing conflict')
        for v,reason in reversed(trail):
            if -v not in out: continue
            new = (out-{-v}) | (reason-{v})
            if new not in graph: graph[new] = (reason,out,v)
            out = new
        if not out <= desired: raise ValueError('invalid resolution expansion')
        clauses[code[0]] = out
        if not out: break
    emitted = {}
    def emit(c):
        if c in emitted: return
        hint = graph[c]
        if hint:
            a,b,v = hint
            emit(a)
            emit(b)
            if v not in a or -v not in b or c != (a-{v})|(b-{-v}): raise ValueError('invalid resolvent')
            step = [list(emitted).index(a),list(emitted).index(b),v]
        else: step = None
        emitted[c]=step
    emit(frozenset())
    return [[sorted(c),step] for c,step in emitted.items()]

if __name__=='__main__':
    bestpath=Path('.pnp/php-best.json')
    best=len(json.loads(bestpath.read_text())) if bestpath.exists() else 10000
    with tempfile.TemporaryDirectory() as tmp:
        for seed in range(int(sys.argv[1]),int(sys.argv[2])):
            proof=search(seed,Path(tmp))
            if len(proof)<best:
                best=len(proof)
                bestpath.write_text(json.dumps(proof))
                print('seed',seed,'length',best,flush=True)
