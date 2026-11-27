# Independent check: Mobius function of the refinement poset of unordered factorizations,
# from the prime factorization (bottom) to [n] (top).
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)

def divisor_pairs(f):
    out=[]
    d=2
    while d*d<=f:
        if f%d==0: out.append((d,f//d))
        d+=1
    return out

@lru_cache(None)
def down(x):
    """All refinements of factorization x (sorted tuple), including x."""
    s={x}
    for i,f in enumerate(x):
        if i>0 and x[i-1]==f: continue
        rest=x[:i]+x[i+1:]
        for a,b in divisor_pairs(f):
            y=tuple(sorted(rest+(a,b)))
            s|=down(y)
    return frozenset(s)

def mu_bottom_top(n):
    if n==1: return 1
    top=(n,)
    elems=down(top)
    bottom=min(elems,key=len) if False else max(elems,key=len)
    # mu(bottom,x) = -sum_{bottom<=y<x} mu(bottom,y); every element is >= bottom
    order=sorted(elems,key=len,reverse=True)
    mu={}
    for x in order:
        if x==bottom: mu[x]=1
        else: mu[x]=-sum(mu[y] for y in down(x) if y!=x)
    return mu[top], len(elems), len(bottom)

if __name__=="__main__":
    for n in [5,8,12,16,24,36,72,2**4*3**2,2**3*3**3]:
        print(n, mu_bottom_top(n))
    print("93312", mu_bottom_top(2**7*3**6))
