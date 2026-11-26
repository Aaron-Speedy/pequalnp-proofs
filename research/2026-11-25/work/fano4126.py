from pathlib import Path
import re,json
d=Path('.pnp');s=Path('lean/PEqualNP/Outside/R_meta_4125_52.lean').read_text()
name='LocalFano4126.fromPacked'
(d/'FanoPacked4126.lean').write_text(re.sub(r'\b27\b','budget',s.replace('PEqualNP.Outside.R_meta_4125_52',name+' (budget : ℕ)')))
gs=[]
def gate(op,a,b):
 assert a!=b and max(a,b)<14+len(gs)
 gs.append((op,a,b));return 13+len(gs)
stars=[];r=2
for p in range(7):
 ns=[7+l for l in range(7) if (p-l)%7 in (0,1,3)]
 v=gate(1,gate(1,ns[0],ns[1]),ns[2])
 if p==r:miss=v
 else:stars.append(gate(0,p,v))
h=stars[0]
for term in stars[1:]:h=gate(1,h,term)
out=gate(0,gate(1,h,r),gate(1,h,miss))
initial=json.loads(re.search(r'let initial := \((\[[0-9,]+\])',s)[1])
vals=initial[:]
for op,a,b in gs:
 x,y=vals[a],vals[b]
 vals.append(x|y if op else ((x&y&1729382256910270463)|(((x<<1)&y | x&(y<<1))&2882303761517117440)))
assert vals[out]==2097151 and len(gs)==28
(d/'fano4126.json').write_text(json.dumps([gs,out]))
stmt=Path('lean/PEqualNP/Outside/L_meta_4126.lean').read_text().split('L_meta_4126 : (¬ (',1)[1].split(')) := by\n  sorry',1)[0].replace('≤ (27 : ℕ)','≤ (28 : ℕ)')
proof='import FanoPacked4126\nimport PEqualNP.Outside.L_meta_6371\nnamespace LocalFano4126\nset_option maxRecDepth 16000\nset_option maxHeartbeats 2500000\ntheorem witness28 : ('+stmt+') := by\n  apply fromPacked 28 PEqualNP.Outside.L_meta_6371\n  refine ⟨['+','.join('('+('true' if op else 'false')+f',{a},{b})' for op,a,b in gs)+f'],{out},?_,?_,?_⟩ <;> decide +kernel\nend LocalFano4126\n#print axioms LocalFano4126.witness28\n'
(d/'FanoWitness4126.lean').write_text(proof)
print('28 gates; 21 positive, 37 maximal negative and both linear parts checked')
