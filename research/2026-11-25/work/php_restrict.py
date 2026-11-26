from collections import Counter
from php_verify_bound import cert

def set_pigeon(graph, p, h):
    values={4*i+j: i==p and j==h for i in range(5) for j in range(4) if i==p or j==h}
    result={}
    image={}
    for c,edge in graph.items():
        if any(v in values and values[v] != bool(s) for v,s in c):
            image[c]=None
            continue
        reduced=frozenset((v,s) for v,s in c if v not in values)
        if edge is None: image[c]=reduced;result[reduced]=None;continue
        a,b,v=edge
        x,y=image[a],image[b]
        if v in values:
            z=y if values[v] else x
        elif (v,0) not in x: z=x
        elif (v,1) not in y: z=y
        else:
            z=(x-{(v,0)})|(y-{(v,1)})
            result.setdefault(z,(x,y,v))
        assert z<=reduced
        image[c]=z
    retained={}
    def emit(c):
        if c in retained:return
        edge=result[c]
        if edge:
            a,b,v=edge
            emit(a);emit(b)
            assert (v,0) in a and (v,1) in b and c==(a-{(v,0)})|(b-{(v,1)})
        retained[c]=edge
    emit(frozenset())
    return retained

if __name__=='__main__':
    g=cert()
    print('lengths after fixing one pigeon:',Counter(len(set_pigeon(g,p,h)) for p in range(5) for h in range(4)))
    for p in range(5):
        r=set_pigeon(g,p,0)
        print('pigeon',p,'axioms',sum(not h for h in r.values()),'nonaxiom inferences',sum(bool(h) for h in r.values()))
