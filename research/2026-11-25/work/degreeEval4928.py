from pathlib import Path
ns={}
exec(Path('.pnp/nearFano4126.py').read_text().split('for r in (2,4,5,6)')[0],ns)
low=(1<<58)-1
mask=(1<<14)-1
initial=[(v&low)|(1<<(58+i)) for i,v in enumerate(ns['initial'])]
def evaluate(gs):
    wires=initial[:]
    for op,a,b in gs:
        x,y=wires[a],wires[b]
        dep=(x|y)&~low
        if not op:dep|=(((x&y)>>58)&mask)<<72
        wires.append(dep|((x|y if op else x&y)&low))
    return wires
def hits(x):
    return [(i,j) for i in range(7) for j in range(7) if (i-j)%7 in (0,1,3) and x>>(72+i)&1 and x>>(79+j)&1]
def good(x):return x&low==ns['want'] and bool(hits(x))
