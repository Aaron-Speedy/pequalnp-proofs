"""Compute axiom-dependency lower bounds for small clauses under PHP."""
from itertools import combinations
from collections import Counter
from php_critical import witnesses
from php_verify_bound import cert

def critical_masks(h):
    cases=list(witnesses(h))
    variables=h*(h+1)
    # Bit i means the i-th assignment falsifies that literal.
    masks = { (v,s):sum(1<<i for i,(pat,_) in enumerate(cases) if (v in pat)==bool(s))
              for v in range(variables) for s in range(2) }
    banks = [sum(1<<i for i,(_,b) in enumerate(cases) if b==j) for j in range(max(b for _,b in cases)+1)]
    return masks,banks,(1<<len(cases))-1

def rank(c,masks,banks,all_cases):
    common=all_cases
    for literal in c:common &= masks[literal]
    return sum(bool(common & bank) for bank in banks)

if __name__ == '__main__':
    masks,banks,all_cases=critical_masks(4)
    g=cert();steps=0; earliest={}
    for c,h in g.items():
        if h:
            steps+=1
            k=rank(c,masks,banks,all_cases)
            assert k<=steps+1
            earliest.setdefault(len(c),(steps,k))
    for w in (0,1,2,3):
        ranks=[rank(c,masks,banks,all_cases) for c in combinations(masks,w)
               if len({v for v,s in c})==w]
        print('width',w,'required distinct axioms',min(ranks),'to',max(ranks))
    for sign in (0,1):
        k=rank([(0,sign)],masks,banks,all_cases)
        print('unit',('positive','negative')[sign],k,'axioms;',k-1,'inferences')
    print('known proof earliest (inference, required axioms) by width:',earliest)
