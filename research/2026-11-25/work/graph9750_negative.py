"""Find a size-preserving first use of NOT in a known optimal monotone layout."""
from graph9750_windows import *
def test(gs):
    w=run(gs);users=[set() for _ in w]
    for i,(_,a,b) in enumerate(gs,12):users[a].add(i);users[b].add(i)
    count=0
    for out in range(12,len(w)):
        cm=run(gs,(out,0))[-1]^run(gs,(out,allrows))[-1]
        wanted=w[out]&cm
        choices=[{out}]+[{z,out} for z in gs[out-12][1:] if z>=12 and users[z]=={out}]
        for block in choices:
            count+=1
            invalid=set(block)
            for a,(_,i,j) in enumerate(gs,12):
                if i in invalid or j in invalid:invalid.add(a)
            bank={v&cm:i for i,v in enumerate(w) if i not in invalid}
            for a,i in bank.items():
                if cm^a==wanted:return count,(gs,sorted(block),out,[('not',i,i)])
                if len(block)==1:continue
                for b,j in bank.items():
                    if i==j:continue
                    for op,v in [('and',a&b),('or',a|b)]:
                        if v^cm==wanted:return count,(gs,sorted(block),out,[(op,i,j),('not','new','new')])
                    if ((a^cm)&b)==wanted:return count,(gs,sorted(block),out,[('not',i,i),('and','new',j)])
                    if ((a^cm)|b)==wanted:return count,(gs,sorted(block),out,[('not',i,i),('or','new',j)])
    return count,None
if __name__=='__main__':
    rng=random.Random(9750);count=0
    for i in range(300):
        n,answer=test(star(rng,i%2));count+=n
        if answer: print('WITNESS',json.dumps(answer),flush=True);break
        if i%25==24:print(i+1,count,flush=True)
