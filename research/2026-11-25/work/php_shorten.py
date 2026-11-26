"""Shrink a resolution DAG by replacing individual derivations with unit traces."""
import json
from pathlib import Path
import random
import re
import time

def original():
    text=Path('lean/PEqualNP/Outside/L_pcx_171.lean').read_text().split('def cert :')[1].split('theorem hc')[0]
    rows=[line for line in text.splitlines() if line.strip().startswith('(')]
    graph={}
    ordered=[]
    for line in reversed(rows):
        clause=frozenset((4*int(a)+int(b)+1)*(1 if sign=='true' else -1)
                         for a,b,sign in re.findall(r'\(\((\d+), (\d+)\), (true|false)\)',line))
        match=re.search(r'some \((\d+), (\d+), \((\d+), (\d+)\)\)',line)
        hint=None
        if match:
            a,b,i,j=map(int,match.groups())
            hint=(ordered[-1-a],ordered[-1-b],i*4+j+1)
        graph[clause]=hint
        ordered.append(clause)
    return graph

def trim(graph):
    kept={}
    def descend(c):
        if c in kept: return
        hint=graph[c]
        if hint:
            a,b,v=hint
            descend(a);descend(b)
            assert v in a and -v in b and c==(a-{v})|(b-{-v})
        kept[c]=hint
    descend(frozenset())
    return kept

def write(graph,path):
    ids={c:i for i,c in enumerate(graph)}
    path.write_text(json.dumps([[sorted(c),[ids[h[0]],ids[h[1]],h[2]] if h else None] for c,h in graph.items()]))

def rup(goal,context):
    true={-v for v in goal}
    trail=[]
    while True:
        progress=False
        for c in context:
            if not c.isdisjoint(true): continue
            fresh=[v for v in c if -v not in true]
            if len(fresh)>1: continue
            if not fresh:
                out=c
                made={}
                for v,reason in reversed(trail):
                    if -v not in out: continue
                    new=(out-{-v})|(reason-{v})
                    if new not in made and new not in context: made[new]=(reason,out,v)
                    out=new
                return made if out==goal and goal in made else None
            pivot,=fresh
            true.add(pivot);trail.append((pivot,c));progress=True
        if not progress: return None

best=trim(original())
path=Path('.pnp/php-short.json')
if path.exists():
    loaded={}
    lines=[]
    for xs,h in json.loads(path.read_text()):
        c=frozenset(xs);loaded[c]=(lines[h[0]],lines[h[1]],h[2]) if h else None
        lines.append(c)
    best=trim(loaded)
print('starting with',len(best),'lines',flush=True)
rng=random.Random(167)
start=time.monotonic()
current=best
attempts=0
while time.monotonic()-start<200:
    attempts+=1
    if attempts%250==0: current=best
    candidates=[c for c,h in current.items() if h]
    goal=rng.choice(candidates)
    before=list(current)[:list(current).index(goal)]
    # All axioms are freely reorderable; unrelated inferences may also be used
    # when their dependency cones avoid the line being replaced.
    depends={goal}
    for c,h in current.items():
        if h and (h[0] in depends or h[1] in depends): depends.add(c)
    before=[c for c in current if c not in depends]
    rng.shuffle(before)
    if rng.random()<0.75:
        a,b,_=current[goal]
        remove=rng.choice([a,b])
        before=[c for c in before if c!=remove]
    replacement=rup(goal,before)
    if not replacement: continue
    g=dict(current)
    for c,h in replacement.items():
        if c not in g or c==goal: g[c]=h
    try: new=trim(g)
    except RecursionError: continue
    if len(new)<len(best):
        best=new;write(best,path);print('attempt',attempts,'best',len(best),flush=True)
    if len(new)<=len(current) or (len(new)<=len(best)+3 and rng.random()<0.03): current=new
print('attempts',attempts,'best',len(best),flush=True)
