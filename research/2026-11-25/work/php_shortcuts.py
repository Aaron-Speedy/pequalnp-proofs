"""Search for subsuming resolution shortcuts, propagating stronger clauses."""
from pathlib import Path
from php_verify_bound import cert
from collections import defaultdict
import random, time, json

MASK=(1<<20)-1
def flip(c): return ((c&MASK)<<20)|(c>>20)
def resolve(a,b):
    opposing=a&flip(b)
    if not opposing or opposing & (opposing-1): return None
    i=(opposing & MASK or opposing >> 20).bit_length()-1
    out=(a|b)&~((1<<i)|(1<<(20+i)))
    return out, (a,b,i) if a>>i&1 else (b,a,i)

def normalize(g):
    done={}
    def visit(c):
        if c in done: return done[c]
        h=g[c]
        if h is None: out=c; why=None
        else:
            a,b,i=h
            x,y=visit(a),visit(b)
            if not x>>i&1: out=x;why=None
            elif not y>>(i+20)&1: out=y;why=None
            else: out,why=resolve(x,y)
        if why or h is None: new.setdefault(out,why)
        done[c]=out;return out
    new={}
    assert visit(0)==0
    used=set()
    def mark(c):
        if c in used:return
        used.add(c)
        if new[c]:
            a,b,i=new[c];mark(a);mark(b)
    mark(0)
    return {c:h for c,h in new.items() if c in used}

def initial():
    def mask(c):return sum(1<<(i+s*20) for i,s in c)
    return normalize({mask(c): (mask(h[0]),mask(h[1]),h[2]) if h else None for c,h in cert().items()})

def scan(g,rng):
    lines=list(g)
    ids={c:i for i,c in enumerate(lines)}
    dep={}
    for c,h in g.items():
        dep[c]=1<<ids[c]
        if h: dep[c]|=dep[h[0]]|dep[h[1]]
    # Index possible goals by a literal contained in the replacement.
    index={k:[c for c in g if g[c] and (c>>k)&1] for k in range(40)}
    def applicable(out,anc):
        targets=index[(out&-out).bit_length()-1] if out else g
        for c in targets:
            if g[c] and not out & ~c and not anc>>ids[c]&1:yield c
    one={}
    for j,a in enumerate(lines):
        for b in lines[:j]:
            r=resolve(a,b)
            if r is None:continue
            out,h=r
            anc=dep[a]|dep[b]
            if out not in g: one.setdefault(out,(h,anc))
            for c in applicable(out,anc):
                if h==g[c]:continue
                new=normalize(g|{c:h})
                if len(new)<len(g):return new
                if len(new)==len(g) and rng.randrange(180)==0:return new
    candidates=list(one.items());rng.shuffle(candidates)
    for mid,(left,anc) in candidates:
        for b in lines:
            r=resolve(mid,b)
            if r is None:continue
            out,h=r
            for c in applicable(out,anc|dep[b]):
                new=normalize(g|{mid:left,c:h})
                if len(new)<len(g):return new
                if len(new)==len(g) and rng.randrange(300)==0:return new
    return g

if __name__=='__main__':
    best=initial(); current=best; rng=random.Random(166)
    start=time.monotonic()
    it=0
    while time.monotonic()-start<420:
        current=scan(current,rng);it+=1
        if len(current)<len(best):
            best=current
            Path('.pnp/php-shortcut-best.json').write_text(json.dumps(best))
            print('scan',it,'best',len(best),flush=True)
        if it%40==0:current=best
    print('scans',it,'best',len(best),flush=True)
