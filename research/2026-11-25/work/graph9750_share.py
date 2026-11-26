"""Search replacements with connections to arbitrary independent wires."""
from graph9750_windows import *
def search(gs):
    w=run(gs);total=0
    users=[set() for _ in w]
    for i,(_,a,b) in enumerate(gs,12):users[a].add(i);users[b].add(i)
    for out in range(12,len(w)):
        cm=run(gs,(out,0))[-1]^run(gs,(out,allrows))[-1]
        target=w[out]&cm
        stack=[frozenset([out])]; seen=set(stack)
        while stack:
            block=stack.pop()
            leaves={j for i in block for j in gs[i-12][1:] if j not in block}
            if len(block)<3:
                for z in leaves:
                    if z>=12 and users[z]<=block:
                        new=block|{z}
                        if new not in seen:seen.add(new);stack.append(new)
            if len(block)<2:continue
            invalid=set(block)
            for a,(_,i,j) in enumerate(gs,12):
                if i in invalid or j in invalid:invalid.add(a)
            avail={}
            for i,v in enumerate(w):
                if i not in invalid:avail.setdefault(v&cm,i)
            ops={v:('wire',i) for v,i in avail.items()}
            for a,i in avail.items():
                ops.setdefault(cm^a,('not',i,i))
                for b,j in avail.items():
                    if j>=i:continue
                    ops.setdefault(a&b,('and',i,j));ops.setdefault(a|b,('or',i,j))
            ans=[ops[target]] if target in ops else None
            if ans is None and len(block)==3:
                if cm^target in ops:ans=[ops[cm^target],('not','new','new')]
                else:
                    for b,j in avail.items():
                        can_and=b&target==target
                        can_or=b|target==target
                        if not(can_and or can_or):continue
                        for a,node in ops.items():
                            if can_and and a&b==target:ans=[node,('and','new',j)];break
                            if can_or and a|b==target:ans=[node,('or','new',j)];break
                        if ans:break
            total+=1
            if ans:return total,(gs,sorted(block),out,ans)
    return total,None
if __name__=='__main__':
    rng=random.Random(9750);count=0
    for i in range(600):
        used,witness=search(star(rng,i%2));count+=used
        if witness:print('WITNESS',json.dumps(witness),flush=True);break
        if i%50==49:print(i+1,count,flush=True)
