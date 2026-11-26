import itertools,json
from pathlib import Path
rows=json.loads(Path('.pnp/rect10005-rows.json').read_text())
lines=[frozenset(i for i,r in enumerate(rows) if r>>j&1) for j in range(31)]
P=set(range(31))
def norm(v):
    v=tuple(n%5 for n in v); lead=next(n for n in v if n)
    return tuple(n*pow(lead,-1,5)%5 for n in v)
def coords():
    infinity=lines[0];origin=min(P-infinity)
    dx,dy=sorted(infinity)[:2]
    def line(p,q):return next(l for l in lines if p in l and q in l)
    def axis(d):return sorted(line(origin,d)-{origin,d})
    xs,ys=axis(dx),axis(dy)
    for xp in itertools.permutations(xs[1:]):
        for yp in itertools.permutations(ys[1:]):
            point={}
            for x,px in enumerate([origin,xs[0],*xp]):
                for y,py in enumerate([origin,ys[0],*yp]):
                    p,=line(px,dy)&line(py,dx)
                    point[p]=(x,y,1)
            for d in infinity:
                p=next(iter(line(d,origin)-{origin,d}))
                point[d]=(*point[p][:2],0)
            c={p:norm(v) for p,v in point.items()}
            def det(a,b,c):
                return sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3]) for i in range(3))%5
            if all(all(not det(c[a],c[b],c[p]) for p in l) for l in lines for a,b in [sorted(l)[:2]]):return c
    raise ValueError('coordinates unavailable')
def generator(c,mat):
    index={q:p for p,q in c.items()}
    point=[index[norm([sum(a*b for a,b in zip(r,c[i])) for r in mat])] for i in range(31)]
    lineids={l:j for j,l in enumerate(lines)}
    line=[lineids[frozenset(point[i] for i in l)] for l in lines]
    assert all(((rows[i]>>j)&1)==((rows[point[i]]>>line[j])&1) for i in range(31) for j in range(31))
    return point,line
if __name__=='__main__':
    c=coords()
    group={k:generator(c,m) for k,m in {'ord5':[[1,1,0],[0,1,1],[0,0,1]],'ord3':[[0,4,0],[1,4,0],[0,0,1]],'elation':[[1,1,0],[0,1,0],[0,0,1]]}.items()}
    for name,(r,l) in group.items():
        print(name,'fixed:',sum(i==j for i,j in enumerate(r)),sum(i==j for i,j in enumerate(l)))
        Path('.pnp/plane10005-'+name+'.dat').write_text(' '.join(map(str,r+l))+'\n')
