from php_shortcuts import *
import re
p=Path('lean/PEqualNP/Outside/L_pcx_153.lean').read_text()
clauses=[sum(1<<(3*int(a)+int(b)+(0 if s=='true' else 20)) for a,b,s in re.findall(r'\(\((\d+), (\d+)\), (true|false)\)',line)) for line in re.findall(r'^def l\d+ : Clause VV := (.*)$',p,re.M)]
g={x:None for x in clauses[:22]}
for i,a,b in re.findall(r'theorem d(\d+) :[^\n]+\n  IsDerivation.res \(C := l(\d+)\) \(D := l(\d+)\)',p):
 x,h=resolve(clauses[int(a)],clauses[int(b)])
 assert x==clauses[int(i)]
 g[x]=h
best=normalize(g)
print('initial',len(best),flush=True)
if __name__=='__main__':
 cur=best;r=random.Random(151);end=time.monotonic()+180
 while time.monotonic()<end and len(best)>51:
    cur=scan(cur,r)
    if len(cur)<len(best):
        best=cur
        Path('.pnp/php4-shorter.json').write_text(json.dumps(best));print('improved',len(best),flush=True)
    if r.randrange(100)==0:cur=best
