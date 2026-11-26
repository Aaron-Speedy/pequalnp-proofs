from pathlib import Path
import sys
def check(base):
    clauses={}
    with base.with_suffix('.cnf').open() as f:
        header=f.readline().split()
        assert header[:2]==['p','cnf']
        for i,line in enumerate(f,1):
            vals=list(map(int,line.split()));assert vals.pop()==0
            clauses[i]=vals
        assert len(clauses)==int(header[3])
    latest=len(clauses);count=0
    with base.with_suffix('.lrat').open() as f:
        for line in f:
            fields=line.split()
            if fields[1]=='d':
                for i in fields[2:-1]:clauses.pop(int(i),None)
                continue
            d=list(map(int,fields));idx=d.pop(0);assert idx>latest
            latest=idx;s=d.index(0);cand=d[:s];hints=d[s+1:-1];assert d[-1]==0
            assert all(i>0 for i in hints)
            units={-lit for lit in cand}
            conflict=any(-l in units for l in units)
            for h in hints:
                if conflict:break
                c=clauses[h]
                assert not any(l in units for l in c)
                available={l for l in c if -l not in units}
                assert len(available)<=1
                if not available:conflict=True
                else:units.update(available)
            assert conflict
            clauses[idx]=cand;count+=1
            if not cand:
                print(base.name,count,'checked additions ending in empty clause');return
    raise ValueError('no empty clause')
for p in sys.argv[1:]:check(Path(p))
