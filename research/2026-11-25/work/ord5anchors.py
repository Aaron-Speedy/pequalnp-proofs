from plane10005 import *
c=coords()
group=[generator(c,[[1,b,d],[0,1,b],[0,0,1]]) for b in range(5) for d in range(5)]
def perm(mask,p):
    return sum(1<<p[k] for k in range(31) if mask>>k&1)
big=set(map(tuple,json.loads(Path('.pnp/conics10005.json').read_text())))
with open('.pnp/ord5anchors.dat','w') as f:
    while big:
        r,l=min(big)
        print(r,l,file=f)
        orbit={(perm(r,p),perm(l,q)) for p,q in group}
        assert orbit<=big
        big-=orbit
