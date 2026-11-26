import re,json,pathlib,collections
D=json.load(open('.pnp/public-gaps-latest.json'));norm=lambda s:re.sub(r'\s+','',s)
goals=collections.defaultdict(list)
for x in D['gaps']:
 if x.get('statement') and not x.get('pr_open'):goals[norm(x['statement'])].append(x['id'])
hit=[]
for x in D['checked']:
 p=pathlib.Path(x['file'])
 if not p.is_file():continue
 s=p.read_text()
 name=x['id'].replace('-','_')
 m=re.search(r'(?:theorem|lemma)\s+(?:PEqualNP\.Outside\.)?'+name+r'\s*:\s*',s)
 if m:
  st=s[m.end():]
  for a in re.finditer(r':=\s*(?:by\b|\n)',st):
   g=goals.get(norm(st[:a.start()]))
   if g:hit.append((g,x['id']))
print(hit[:80])
