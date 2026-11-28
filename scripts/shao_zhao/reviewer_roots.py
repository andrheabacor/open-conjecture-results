# Reviewer check: max |z+1| over connected-domination roots vs the claimed bound 4n/max(1,2δ+2−n).
import itertools, random
import numpy as np
def cd_poly(n, adj):
    c=[0]*(n+1)
    full=(1<<n)-1
    nb=[0]*n
    for v in range(n):
        for u in adj[v]: nb[v]|=1<<u
    for S in range(1,1<<n):
        # dominating
        dom=S
        for v in range(n):
            if S>>v&1: dom|=nb[v]
        if dom!=full: continue
        # connected induced
        start=(S&-S); seen=start; frontier=start
        while frontier:
            v=(frontier&-frontier).bit_length()-1; frontier&=frontier-1
            new=nb[v]&S&~seen; seen|=new; frontier|=new
        if seen==S: c[bin(S).count('1')]+=1
    return c
def connected(n,adj):
    seen={0}; st=[0]
    while st:
        v=st.pop()
        for u in adj[v]:
            if u not in seen: seen.add(u); st.append(u)
    return len(seen)==n
worst=0; tot=0
def check(n,edges):
    global worst,tot
    adj=[set() for _ in range(n)]
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    if not connected(n,adj): return
    c=cd_poly(n,adj); roots=np.roots(c[::-1]) if any(c[1:]) else []
    d=min(len(a) for a in adj); bound=4*n/max(1,2*d+2-n)
    m=max((abs(z+1) for z in roots),default=0)
    tot+=1; worst=max(worst,m/bound)
    if m>bound+1e-9: print("VIOLATION",n,edges,m,bound)
for n in range(2,7):
    E=list(itertools.combinations(range(n),2))
    for mask in range(1<<len(E)):
        check(n,[E[i] for i in range(len(E)) if mask>>i&1])
random.seed(1)
for _ in range(3000):
    n=random.randint(7,12); p=random.random()
    E=[e for e in itertools.combinations(range(n),2) if random.random()<p]
    check(n,E)
print("graphs checked:",tot,"max (max|z+1|)/bound =",round(worst,4))
