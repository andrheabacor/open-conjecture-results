"""Independent witness check by splitting divisors, then adding the lower Möbius column.

The certificate for Lean is generated separately using forward pair mergers.
"""
from functools import cache
from itertools import combinations
from math import isqrt,prod
from pathlib import Path

@cache
def multiplicative_parts(n, lower=2):
    out=[(n,)] if n>=lower else []
    for d in range(lower,isqrt(n)+1):
        if n%d==0:
            out.extend((d,)+xs for xs in multiplicative_parts(n//d,d))
    return out

@cache
def splittings(n):
    return [(d,n//d) for d in range(2,isqrt(n)+1) if n%d==0]

def certify(n):
    rows=sorted(multiplicative_parts(n), key=lambda x:(-len(x),x))
    index={r:i for i,r in enumerate(rows)}
    lower=[]
    lower_values=[]
    masks={}
    groups={}
    for i,x in enumerate(rows):
        proper=0
        for j,t in enumerate(x):
            for a,b in splittings(t):
                y=tuple(sorted(x[:j]+x[j+1:]+(a,b)))
                proper|=lower[index[y]]
        v=1 if i==0 else -sum(a*(bits&proper).bit_count() for a,bits in masks.items())
        lower.append(proper | (1<<i));lower_values.append(v);masks[v]=masks.get(v,0)|(1<<i)
        lev=groups.setdefault(len(x),[0,0,0]);lev[0]+=1;lev[1]+=v;lev[2]+=int(v!=0)
    print("n",n,"factorizations",len(rows),"comparable ordered pairs",sum(b.bit_count() for b in lower))
    print("factor count | nodes | sum mu(bottom,x) | nonzero");print(*[(k,*v) for k,v in sorted(groups.items())],sep='\n')
    print("mu(bottom,top)",lower_values[-1])
    return rows,lower_values

if __name__=="__main__":certify(2**7*3**6)
