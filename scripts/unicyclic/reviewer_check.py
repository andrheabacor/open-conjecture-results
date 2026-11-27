from itertools import combinations
def closure(adj, S):
    col=set(S); changed=True
    while changed:
        changed=False
        for v in list(col):
            un=[u for u in adj[v] if u not in col]
            if len(un)==1: col.add(un[0]); changed=True
    return col
def connected(adj,S):
    S=set(S)
    if not S: return False
    st=[next(iter(S))]; seen={st[0]}
    while st:
        v=st.pop()
        for u in adj[v]:
            if u in S and u not in seen: seen.add(u); st.append(u)
    return seen==S
def poly(n,edges):
    adj={v:set() for v in range(n)}
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    c=[0]*(n+1)
    for k in range(1,n+1):
        for S in combinations(range(n),k):
            if connected(adj,S) and len(closure(adj,S))==n: c[k]+=1
    return c
def lc_fail(c):
    return [(j,c[j-1],c[j],c[j+1]) for j in range(1,len(c)-1) if c[j]>0 and c[j]**2<c[j-1]*c[j+1]]
# sanity vs paper: path P_n and star
print("P5:",poly(5,[(i,i+1) for i in range(4)]))
print("star K1,4:",poly(5,[(0,i) for i in range(1,5)]))
G=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(5,6)]
c=poly(7,G); print("C5 + 2-edge tail:",c,"log-concavity failures:",lc_fail(c))
