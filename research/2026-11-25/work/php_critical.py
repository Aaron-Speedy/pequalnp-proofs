"""Add necessary cut conditions witnessed by assignments falsifying one axiom."""
from itertools import permutations
from pathlib import Path
import sys,tempfile,shutil
from php_bound import CNF,axiom_rows

def witnesses(h):
    rows = axiom_rows(h)
    pats=set()
    for missing in range(h+1):
        for match in permutations(range(h)):
            pts=[p for p in range(h+1) if p!=missing]
            occupied={p*h+x for p,x in zip(pts,match)}
            pats.add(frozenset(occupied))
            for hole in range(h):pats.add(frozenset(occupied|{missing*h+hole}))
    for pat in sorted(pats,key=lambda p:tuple(sorted(p))):
        unsat=[idx for idx,row in enumerate(rows) if all((v in pat)==bool(sign) for v,sign in row)]
        assert len(unsat)==1
        yield pat,unsat[0]

def layout(h,length):
    nvars=h*(h+1)
    nax=len(axiom_rows(h))
    next_id=length*2*nvars+1
    def alloc(n):
        nonlocal next_id
        r=range(next_id,next_id+n);next_id+=n;return r
    steps=[]
    for i in range(nax,length):
        piv=alloc(nvars);alloc(nvars-1)
        parents=[]
        for side in range(2):
            parents.append(alloc(i));alloc(i-1);alloc(2*nvars)
        steps.append((piv,parents))
    return next_id-1,steps

def addcuts(h,length,cnf,model=None):
    axes=axiom_rows(h);nvars=h*(h+1)
    base,steps=layout(h,length);cnf.variables=base
    for pat,row_id in witnesses(h):
        row=axes[row_id]
        row_side=next(iter(row))[1]
        crossings={v:[] for v,_ in row}
        boundary=[]
        for i,(piv,parents) in enumerate(steps,len(axes)):
            # May mark a line as false only when every literal is false under pat.
            false_line=cnf.new()
            satbits=[(i*2*nvars+2*v+(v not in pat)+1) for v in range(nvars)]
            for b in satbits:cnf.add(-false_line,-b)
            if model is not None:model.append(not any(model[b] for b in satbits))
            def mark(trigger):
                k=cnf.new()
                cnf.add(-k,trigger);cnf.add(-k,false_line)
                if model is not None:model.append(model[trigger] and model[false_line])
                return k
            boundary.append(mark(parents[row_side][row_id]))
            for v in crossings:crossings[v].append(mark(piv[v]))
        cnf.add(*boundary)
        for cut in crossings.values():cnf.add(*cut)

def combine(h,length,basepath,out):
    with tempfile.TemporaryFile(mode='w+') as extra:
        cnf=CNF(extra)
        addcuts(h,length,cnf)
        with basepath.open() as old,out.open('w') as new:
            _,_,v,c=old.readline().split()
            assert int(v)==layout(h,length)[0]
            print('p cnf',cnf.variables,int(c)+cnf.clauses,file=new)
            shutil.copyfileobj(old,new)
            extra.seek(0);shutil.copyfileobj(extra,new)
        print('added',cnf.clauses,'clauses;',cnf.variables,'total variables',flush=True)

if __name__=='__main__':
    if sys.argv[1]=='verify':
        from php_verify_bound import model
        bits,length=model()
        with tempfile.TemporaryFile(mode='w+') as extra:
            cnf=CNF(extra);addcuts(4,length,cnf,bits);extra.seek(0)
            assert len(bits)==cnf.variables+1
            for i,line in enumerate(extra,1):
                assert any(bits[abs(v)]==(v>0) for v in map(int,line.split()[:-1])),i
            print('157-line witness satisfies',i,'extra clauses')
    else:combine(int(sys.argv[1]),int(sys.argv[2]),Path(sys.argv[3]),Path(sys.argv[4]))
