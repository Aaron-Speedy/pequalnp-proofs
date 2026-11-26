from plane10005 import *
def cycles(p):
    s=set(range(len(p))); out=[]
    while s:
        i=min(s); z=0
        while i in s:
            s.remove(i);z|=1<<i;i=p[i]
        out.append(z)
    return out
def fixed(name):
    perms=list(map(int,Path('.pnp/plane10005-'+name+'.dat').read_text().split()))
    rs=cycles(perms[:31]); masks=[0]
    for r in rs:masks += [x|r for x in masks]
    m=(1<<31)-1
    rect=set()
    for r in masks[1:]:
        c=m
        for i in range(31):
            if r>>i&1:c&=~rows[i]
        if c:rect.add((sum(1<<i for i in range(31) if rows[i]&c==0),c))
    union=[0]*31
    for r,c in rect:
        for i in range(31):
            if r>>i&1:union[i]|=c
    print(name,len(rect),'fixed total union',sum(v.bit_count() for v in union),'largest areas',sorted([r.bit_count()*c.bit_count() for r,c in rect],reverse=True)[:15])
    return rect
for name in ['ord5','elation','ord3']:
    fixed(name)
for name in ['ord5','elation']:
    with open('.pnp/fixed10005-'+name+'.dat','w') as out:
        for r,c in sorted(fixed(name)): print(r,c,file=out)
