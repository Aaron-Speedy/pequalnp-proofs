import json,re
G=json.load(open('.pnp/public-gaps-latest.json'))['gaps']
for x in G:
 s=x.get('statement','')
 if not s.startswith('¬ (∀') or x.get('pr_open'):continue
 s=s[3:-1].strip()
 level=0;cuts=[]
 for i,v in enumerate(s):
  if v in '([{⟨':level+=1
  elif v in ')]}⟩':level-=1
  elif v=='→' and level==0:cuts.append(i)
 if cuts and re.match(r'\s*∃',s[cuts[-1]+1:]) and ('Nonempty' not in s[:cuts[-1]]):
  end=s[cuts[-1]+1:].strip();print(x['id'],s[:70],end[:75])
