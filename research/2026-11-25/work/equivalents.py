from itertools import permutations
import re,subprocess,sys
target=int(sys.argv[1]); mask=(1<<64)-1
variants={}
for p in permutations(range(6)):
    t=sum((target>>sum((r>>i&1)<<j for i,j in enumerate(p))&1)<<r for r in range(64))
    variants[t]=(p,False)
    variants[int(f'{mask^t:064b}'[::-1],2)]=(p,True)
result=subprocess.run(['rg','--no-heading','-o',r'[0-9]{1,10} \* 2 \^ 32 \+ [0-9]{1,10}','lean/PEqualNP/Outside'],capture_output=True,text=True)
for line in sorted(set(result.stdout.splitlines())):
    path,expr=line.split(':',1)
    a,b=map(int,expr.split(' * 2 ^ 32 + '))
    if (t:=a<<32|b) in variants: print(path,variants[t])
