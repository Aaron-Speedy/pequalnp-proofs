from itertools import combinations
from sys import argv
n=int(argv[1]); budget=int(argv[2])
inputs=tuple(sum(1<<r for r in range(1<<n) if r>>i&1) for i in range(n))
form=[set(inputs)]
seen=set(inputs)
for k in range(1,budget+1):
    nextlayer=set()
    for i in range((k-1)//2+1):
        for a in form[i]:
            for b in form[k-1-i]:
                nextlayer.update((a&b,a|b))
    form.append(nextlayer-seen);seen.update(nextlayer)
states={frozenset()}
leaves=set(inputs)
for k in range(1,budget+1):
    layer=set()
    new=set()
    for state in states:
        stock=leaves|state
        for a,b in combinations(stock,2):
            for v in (a&b,a|b):
                if v not in stock:
                    new.add(v)
                    if k<budget:layer.add(state|{v})
    states=layer
    allowed=set().union(*form[:k+1])
    print(k,'formula reach',len(allowed),'new circuit outputs outside',len(new-allowed),'configurations',len(layer),flush=True)
    if new-allowed:print(sorted(new-allowed)[:10])
