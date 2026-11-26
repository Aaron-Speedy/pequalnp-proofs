from pathlib import Path
import re
d=Path('.pnp')
src=Path('lean/PEqualNP/Outside/L_meta_7537.lean').read_text()
def sect(n):
    a=src.index('lemma '+n+' ')
    b=src.find('\nlemma ',a+1)
    return src[a:b].strip()+'\n'
s='import PEqualNP.Outside.L_meta_7537\nopen PEqualNP.AndCount PEqualNP.Outside.L_meta_7537\nnamespace LocalPack5060\nvariable {C : AndCountCircuit 42} {p q : V → Slot C}\n'
s+='abbrev lowAt (C : AndCountCircuit 42) (v : V) := (positions C v).card ≤ 2\n'
s+='def paired (q : V → Slot C) (v : V) := ∃ w, w ≠ v ∧ q w = q v ∧ lowAt C v ∧ lowAt C w\n'
names={'positions_two':['v'],'shared_adj':['v'],'covered_two':['v'],'mate_pure_card':['v'],'pure_three_card':['a','b'],'mate_on_opposite':['w'],'triple_mixed_separate':[],'triple_mates_opposite':['a','u'],'triple_spare':[]}
for n,low in names.items():
    t=sect(n)
    t=t.replace(' (cap : ∀ v, (positions C v).card ≤ 2)','')
    t=re.sub(r'(\{[a-z ]+ : V\})',lambda m:m[0]+''.join(f' (lo{x} : lowAt C {x})' for x in low),t,count=1)
    t=t.replace('using cap v','using lov')
    # Earlier helper lemmas require only pointwise bounds
    t=t.replace('positions_two layout cap (shared_data layout wv.symm','positions_two layout low (shared_data layout wv.symm')
    t=t.replace('positions_two layout cap (shared_data layout ua.symm','positions_two layout lou (shared_data layout ua.symm')
    t=t.replace('positions_two layout cap','positions_two layout lov')
    for fn,keys in [('shared_adj',{'ua':'a','vb':'b','wc':'c','wv':'v'}),('mate_on_opposite',{'ua':'u','wc':'w'}),('mate_pure_card',{'wc':'w'}),('pure_three_card',{'ab':'loa lob','uv':'lou lov'})]:
        for k,v in keys.items():
            t=t.replace(f'{fn} hc out layout cap {k}',f'{fn} hc out layout '+(v if fn=='pure_three_card' else 'lo'+v)+' '+k)
            t=t.replace(f'{fn} hd layout cap {k}',f'{fn} hd layout lo{v} {k}')
    if n.startswith('triple_'):
        t=t.replace('Shared q ','paired q ')
        for v,w in [('a','u'),('b','v'),('c','w')]:
            t=t.replace(f'⟨{w}, {w}{v}, q{w}⟩ := s{v}',f'⟨{w}, {w}{v}, q{w}, lo{v}, lo{w}⟩ := s{v}')
        t=t.replace('covered_two hc out hd layout cap ⟨u,ua,qu⟩','covered_two hc out hd layout loa ⟨u,ua,qu⟩')
        t=t.replace('covered_two hc out hd layout cap sx','covered_two hc out hd layout (by obtain ⟨_,_,_,h,_⟩ := sx; exact h) (by obtain ⟨w,ne,eq,_,_⟩ := sx; exact ⟨w,ne,eq⟩)')
        for w,v in [('b','v'),('c','w')]:
            t=t.replace(f'covered_two hc out hd layout cap s{w}',f'covered_two hc out hd layout (by obtain ⟨_,_,_,h,_⟩ := s{w}; exact h) (by obtain ⟨w,ne,eq,_,_⟩ := s{w}; exact ⟨w,ne,eq⟩)')
        t=t.replace('triple_mixed_separate hc out hd layout cap','triple_mixed_separate hc out hd layout')
        for a,b,first in [('a','u','ab'),('b','v','ab.symm'),('c','w','ac.symm')]:
            t=re.sub(r'triple_mates_opposite hc out hd layout cap '+re.escape(first)+r' ',f'triple_mates_opposite hc out hd layout lo{a} lo{b} {first} ',t)
        for a,b in [('a','u'),('b','v'),('c','w')]:
            t=t.replace(f'⟨{b},{b}{a},q{b}⟩',f'⟨{b},{b}{a},q{b},lo{a},lo{b}⟩')
        t=t.replace('covered_two hc out hd layout loa ⟨u,ua,qu,loa,lou⟩','covered_two hc out hd layout loa ⟨u,ua,qu⟩').replace('⟨a,ua.symm,qu.symm⟩','⟨a,ua.symm,qu.symm,lou,loa⟩')
    for k in names:
        t=re.sub(r'\b'+k+r'\b','loc_'+k,t)
    s+=t+'\n'
s+='end LocalPack5060\n#print axioms LocalPack5060.loc_triple_spare\n'
(d/'LocalPack5060.lean').write_text(s)
