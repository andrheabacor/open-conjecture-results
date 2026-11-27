"""Exact bottom-to-top Möbius value in the refinement poset of unordered factorizations."""
from itertools import combinations
from time import monotonic
import sys

def poset_value(exponents, size_limit=25000):
    primes = [2, 3, 5, 7, 11, 13, 17, 19]
    start = tuple(p for p,k in zip(primes, exponents) for _ in range(k))
    levels = [[start]]
    covers = {}
    used = 1
    while len(levels[-1][0])>1:
        next_level = set()
        for x in levels[-1]:
            above = set()
            for a,b in combinations(range(len(x)),2):
                if a and x[a-1]==x[a]:continue
                if b>a+1 and x[b-1]==x[b]:continue
                y=tuple(sorted((x[:a]+x[a+1:b]+x[b+1:]+(x[a]*x[b],))))
                above.add(y)
            covers[x]=above
            next_level.update(above)
        used+=len(next_level)
        if used>size_limit:return used,None
        levels.append(sorted(next_level))
    top=levels[-1][0]
    ids={top:0}
    up=[1]
    values=[1]
    # Compress equal interval values into integer bit masks to sum a whole upper set.
    masks={1:1}
    for level in reversed(levels[:-1]):
        for x in level:
            strict=0
            for y in covers.pop(x):strict |= up[ids[y]]
            mu=-sum(v*(m & strict).bit_count() for v,m in masks.items() if v)
            i=len(values);ids[x]=i;up.append(strict | (1<<i));values.append(mu)
            masks[mu]=masks.get(mu,0)|(1<<i)
    return len(values),values[-1]

if __name__ == '__main__':
    for spec in sys.argv[1:]:
        es=tuple(map(int,spec.split(',')));t=monotonic();count,mu=poset_value(es)
        print(es,count,mu,round(monotonic()-t,2),flush=True)
        if mu is not None and mu*(-1)**(sum(es)+1)<0:print('COUNTEREXAMPLE',es,mu,flush=True);break
