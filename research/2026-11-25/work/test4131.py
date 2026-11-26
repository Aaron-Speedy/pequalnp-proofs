from pathlib import Path
exec(Path('.pnp/obstructions4131.py').read_text().split('for d in range')[0])
def closure(v):
    for i in range(16):
        flag=1<<i
        for j in range(65536):
            if j&flag:
                v[j]=max(v[j],v[j^flag])
    return v
exact=[0]*65536
for s in range(2048):
    if any(s&i==i for i in ind):
        j=induced(s)
        exact[j]=max(exact[j],s.bit_count()-4)
exact=closure(exact)
model=[0]*65536
for d in range(7):
    c={induced(s) for s in range(2048) if s.bit_count()==5+d and any(s&i==i for i in ind)}
    for j in c:
        if not any(m!=j and m&j==m for m in c):
            model[j]=max(model[j],d+1)
assert closure(model)==exact
print('Validated the exact cover loss for all',len(exact),'deleted-edge sets.')
print('Loss frequencies:',[exact.count(i) for i in range(8)])
