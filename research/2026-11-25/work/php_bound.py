"""SAT model for bounded, ordinary binary resolution of PHP(h+1,h)."""
import argparse
import itertools
import os
from pathlib import Path
import shutil
import tempfile

class CNF:
    def __init__(self, stream):
        self.variables = 0
        self.clauses = 0
        self.stream = stream

    def new(self):
        self.variables += 1
        return self.variables

    def add(self, *clause):
        self.stream.write(' '.join(map(str, clause)) + ' 0\n')
        self.clauses += 1

    def choice(self, size):
        options = [self.new() for _ in range(size)]
        self.add(*options)
        # The prefixes are also used to order the largest parent of each row.
        prefix = [options[0]]
        for opt in options[1:]:
            prev = prefix[-1]
            head = self.new()
            self.add(-opt, -prev)
            self.add(-opt, head)
            self.add(-prev, head)
            self.add(-head, prev, opt)
            prefix.append(head)
        return options, prefix

def axiom_rows(h):
    pigeons = [[i*h+j for j in range(h)] for i in range(h+1)]
    rows = [{(p,0) for p in pigeon} for pigeon in pigeons]
    return rows + [{(a[j],1), (b[j],1)} for a,b in itertools.combinations(pigeons,2) for j in range(h)]

def encode(h, length, path):
    variables = (h+1)*h
    axioms = axiom_rows(h)
    if length <= len(axioms): raise ValueError('budget needs room for a resolution step')
    with tempfile.TemporaryFile(mode='w+') as stream:
        cnf = CNF(stream)
        rows = [[[cnf.new() for _ in range(2)] for _ in range(variables)] for _ in range(length)]
        for i,c in enumerate(axioms):
            for v in range(variables):
                for sign,lit in enumerate(rows[i][v]):
                    cnf.add(lit if (v,sign) in c else -lit)
        previous = None
        for i in range(len(axioms), length):
            pivot,_ = cnf.choice(variables)
            sides = []
            prefixes = []
            for side in range(2):
                choices, prefix = cnf.choice(i)
                prefixes.append(prefix)
                selected = [[cnf.new() for _ in range(2)] for _ in range(variables)]
                for k,choice in enumerate(choices):
                    if i == len(axioms):
                        # The first inference must use a row and a collision. Relabel
                        # pigeons and holes so the pivot is pigeon zero, hole zero.
                        cnf.add(choice if k == (0 if side==0 else h+1) else -choice)
                    for v in range(variables):
                        for sign in range(2):
                            lit = selected[v][sign]
                            old = rows[k][v][sign]
                            cnf.add(-choice, -lit, old)
                            cnf.add(-choice, lit, -old)
                for v in range(variables):
                    cnf.add(-pivot[v],selected[v][side])
                sides.append(selected)
            if previous:
                # In a topological sort, choose the ready inference with the
                # smallest largest-parent index. Newly ready rows use a newer parent.
                for k in range(len(previous[0])):
                    for prior in previous:
                        cnf.add(-prefixes[0][k],-prefixes[1][k],prior[k])
            previous = prefixes
            for v in range(variables):
                for sign in range(2):
                    own, other = sides[sign][v][sign], sides[1-sign][v][sign]
                    value = rows[i][v][sign]
                    # The pivot is erased only on its designated side.
                    cnf.add(-other, value)
                    cnf.add(-own, pivot[v], value)
                    cnf.add(-value, other, own)
                    cnf.add(-value, other, -pivot[v])
        for pair in rows[-1]:
            for lit in pair: cnf.add(-lit)
        stream.seek(0)
        with path.open('w') as f:
            f.write(f'p cnf {cnf.variables} {cnf.clauses}\n')
            shutil.copyfileobj(stream,f)
        print(f'{path}: {cnf.variables} variables, {cnf.clauses} clauses',flush=True)

if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('holes',type=int);p.add_argument('lines',type=int);p.add_argument('cnf',type=Path)
    a=p.parse_args();encode(a.holes,a.lines,a.cnf)
