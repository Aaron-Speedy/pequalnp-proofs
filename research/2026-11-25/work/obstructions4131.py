from itertools import combinations
edges=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
def induced(s):
    return sum(1<<i for i,(a,b) in enumerate(edges) if s>>a&1 and s>>b&1)
ind=[s for s in range(2048) if s.bit_count()==4 and induced(s)==0]
for d in range(7):
    cand={induced(s) for s in range(2048) if s.bit_count()==5+d and any(s&i==i for i in ind)}
    mins=[]
    for s in sorted(cand,key=int.bit_count):
        if not any(s&m==m for m in mins):
            mins.append(s)
    print(d,len(cand),len(mins),sorted(set(m.bit_count() for m in mins)))
def adj(i,j): return tuple(sorted((i,j))) in edges
def autos(p=()):
    i=len(p)
    if i==11:
        yield p
        return
    for j in range(11):
        if j not in p and sum(adj(j,v) for v in range(11))==sum(adj(i,v) for v in range(11)) and all(adj(i,k)==adj(j,v) for k,v in enumerate(p)):
            yield from autos(p+(j,))
group=list(autos())
print('automorphisms', len(group))
def move(s,p):
    return sum(1<<edges.index(tuple(sorted((p[a],p[b])))) for j,(a,b) in enumerate(edges) if s>>j&1)
for k in range(1,8):
    c={induced(s) for s in range(2048) if s.bit_count()==4+k and any(s&i==i for i in ind)}
    minimal={s for s in c if not any(m!=s and m&s==m for m in c)}
    rep={min(move(s,p) for p in group) for s in minimal}
    print(k,len(rep))
