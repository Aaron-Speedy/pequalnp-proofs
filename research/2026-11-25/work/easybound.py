import re,json,pathlib,collections
D=json.load(open('.pnp/public-gaps-latest.json'))
def parse(s):
 s=re.sub(r'\s+','',s)
 pat=r'(≤|<)(\d+)(?=\)*$)'
 m=re.search(pat,s)
 if not m:return None
 return (s[:m.start(2)]+s[m.end(2):],int(m[2]))
goals=collections.defaultdict(list)
for x in D['gaps']:
 if x.get('statement') and not x.get('pr_open'):
  z=parse(x['statement'])
  if z:goals[z[0]].append((z[1],x['id']))
for x in D['checked']:
 p=pathlib.Path(x['file'])
 if not p.is_file():continue
 s=p.read_text();name=x['id'].replace('-','_')
 m=re.search(r'(?:theorem|lemma)\s+(?:PEqualNP\.Outside\.)?'+name+r'\s*:\s*',s)
 if not m:continue
 st=s[m.end():]
 a=re.search(r':=\s*by\b',st)
 if not a:continue
 z=parse(st[:a.start()])
 if z:
  for v,i in goals.get(z[0],[]):
   if (v<z[1] if z[0].startswith('¬') else v>z[1]):print(i,v,x['id'],z[1])
