import itertools
from pathlib import Path
P=[3,6,12,17,24,33,66,132,160,264,288,320,528,576,640]
N=[50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
Z=[r for r in N if not r&1]
def permute(b,perm):
 return sum(((b>>k)&1)<<p for k,p in enumerate(perm))
# Preserve adjacency, which lets us prune almost all coordinate permutations early.
edge={tuple(i for i in range(10) if m>>i&1) for m in P}
def adjacent(i,j):return tuple(sorted((i,j))) in edge
G=[]
def dfs(old):
 k=len(old)
 if k==10:
  assert {permute(i,old) for i in N}==set(N)
  G.append(old);return
 for x in range(1,10):
  if x not in old and all(adjacent(i,k)==adjacent(y,x) for i,y in enumerate(old)):dfs(old+[x])
dfs([0])
reps=[];left={i for i in P if i%2==0};chosen={}
while left:
 t=min(left);reps.append(t)
 for g in G:
  j=permute(t,g);chosen[j]=(t,g);left.discard(j)
print('group order',len(G),'representatives',reps)
print('representative, all members',[(r,sorted(k for k,v in chosen.items() if v[0]==r)) for r in reps])
