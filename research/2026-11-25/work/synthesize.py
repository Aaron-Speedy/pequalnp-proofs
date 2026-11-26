"""Find small AND/OR/NOT circuits by exact SAT synthesis."""
from itertools import combinations
from pathlib import Path
import subprocess
import sys
import tempfile

table, size = map(int, sys.argv[1:3])
mode = sys.argv[3] if len(sys.argv) > 3 else 'general'
monotone = mode == 'monotone'
clauses = []
nvar = 0
def fresh():
    global nvar
    nvar += 1
    return nvar

def one(options):
    clauses.append(options)
    previous = None
    for opt in options[:-1]:
        prefix = fresh()
        clauses.append([-opt, prefix])
        if previous:
            clauses.extend([[-previous, prefix], [-previous, -opt]])
        previous = prefix
    clauses.append([-options[-1], -previous])

outputs = [[fresh() for row in range(64)] for _ in range(6 + size)]
for i in range(6):
    for row, v in enumerate(outputs[i]):
        clauses.append([v if row >> i & 1 else -v])
controls = []
uses = [[] for i in outputs]
for idx in range(6, 6+size):
    sel = {}
    gates = [(op,i,j) for i,j in combinations(range(idx),2) for op in ['and','or']]
    if not monotone:
        gates += [('not',i,i) for i in range(idx)]
    for op,i,j in gates:
        choice = fresh()
        sel[choice] = (op,i,j)
        uses[i].append(choice)
        if j != i:
            uses[j].append(choice)
        for a,b,v in zip(outputs[i],outputs[j],outputs[idx]):
            if op == 'not':
                constraints = [[a,v],[-a,-v]]
            elif op == 'and':
                constraints = [[-a,-b,v],[a,-v],[b,-v]]
            else:
                constraints = [[a,b,-v],[-a,v],[-b,v]]
            clauses.extend([[-choice]+c for c in constraints])
    one(list(sel))
    controls.append(sel)
# Canonically sort ready gates by their highest-numbered parent. Breaking
# ties by operation and parents leaves at least one minimum circuit.
def gate_key(gate):
    op, left, right = gate
    return right, left, op

for first, second in zip(controls, controls[1:]):
    for a, gate_a in first.items():
        for b, gate_b in second.items():
            if gate_key(gate_b) <= gate_key(gate_a):
                clauses.append([-a, -b])
# Every essential variable has a path to the output.
for i in range(6):
    if any((table >> r ^ table >> (r ^ (1 << i))) & 1 for r in range(64)):
        clauses.append(uses[i])
if mode == 'with-not':
    clauses.append([choice for sel in controls for choice, gate in sel.items()
                    if gate[0] == 'not'])
# Only connected circuits are needed at minimum size.
clauses.extend(uses[i] for i in range(6, 6+size-1))
for row,v in enumerate(outputs[-1]):
    clauses.append([v if table>>row&1 else -v])
with tempfile.NamedTemporaryFile(mode='w',suffix='.cnf') as cnf:
    print('p cnf',nvar,len(clauses),file=cnf)
    for c in clauses:
        print(*c,0,file=cnf)
    cnf.flush()
    solver=Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'
    result=subprocess.run([solver,'-q','-t','65',cnf.name],capture_output=True,text=True)
print(size,'monotone' if monotone else 'general', result.returncode)
if result.returncode == 10:
    model={int(x) for line in result.stdout.splitlines() if line.startswith('v ') for x in line.split()[1:]}
    print([sel[next(iter(sel.keys() & model))] for sel in controls])
