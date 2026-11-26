from collections import Counter
from array import array
n=21
mask=(1<<n)-1
N=[sum(1<<((i+d)%n) for d in (0,5,7,17,20)) for i in range(n)]
allowed=array('I',[mask])*(1<<n)
freq=Counter()
for a in range(1<<n):
    if a: allowed[a]=allowed[a&(a-1)]&~N[(a&-a).bit_length()-1]
    b=allowed[a]
    if all((a>>i&1) or b&nb for i,nb in enumerate(N)):
        freq[(a.bit_count(),b.bit_count())]+=1
print(sorted(freq.items()))
print('size 10',sum(v for (p,l),v in freq.items() if p+l==10),'total',sum(freq.values()))
