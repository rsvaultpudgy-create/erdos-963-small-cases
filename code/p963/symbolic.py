# Erdos 963, rigorous small cases over ALL real sets (not just bounded integers).
# Fact: if B is a maximal dissociated subset of S (|B|=k), every other element of S equals +-(eps . b)
# for some eps in {-1,0,1}^k.  So S is a set of linear forms in b=(b_1..b_k).
# We search over all such form-sets and all linear subspaces L (where b lives) for a set S of size >= target
# with no dissociated (k+1)-subset.  Branching on "which {-1,0,1} relation holds" is exhaustive.
import sys, itertools
from fractions import Fraction
from math import gcd
k=int(sys.argv[1]); target=int(sys.argv[2])
def canon_row(v):
    # scale rational vector to primitive integer vector with first nonzero positive
    den=1
    for x in v: den=den*x.denominator//gcd(den,x.denominator)
    iv=[int(x*den) for x in v]
    g=0
    for x in iv: g=gcd(g,abs(x))
    if g==0: return None
    iv=[x//g for x in iv]
    for x in iv:
        if x!=0:
            if x<0: iv=[-y for y in iv]
            break
    return tuple(iv)
def reduce(v,E):
    # E: tuple of (pivot index, row as tuple of Fractions with row[p]==1), RREF
    v=list(v)
    for p,row in E:
        c=v[p]
        if c!=0:
            for j in range(k): v[j]-=c*row[j]
    return v
def add_eq(E,c):
    r=reduce([Fraction(x) for x in c],E)
    p=next((j for j in range(k) if r[j]!=0),None)
    if p is None: return E
    r=[x/r[p] for x in r]
    newE=[]
    for q,row in E:
        cc=row[p]
        if cc!=0: row=tuple(row[j]-cc*r[j] for j in range(k))
        newE.append((q,row))
    newE.append((p,tuple(r)))
    newE.sort()
    return tuple(newE)
signs=[e for e in itertools.product((-1,0,1),repeat=k) if any(e)]
half=[e for e in signs if next(x for x in e if x)>0]          # forms up to sign
units=[tuple(1 if i==j else 0 for j in range(k)) for i in range(k)]
cands=[e for e in half if e not in units]
deltas=[d for d in itertools.product((-1,0,1),repeat=k+1) if any(d) and next(x for x in d if x)>0]
def iszero(v): return all(x==0 for x in v)
def valid(E,S):
    for e in half:
        if iszero(reduce(e,E)): return False          # B not dissociated (or b=0)
    red=[reduce(v,E) for v in S]
    for i in range(len(S)):
        for j in range(i):
            if all(red[i][t]==red[j][t] for t in range(k)) or all(red[i][t]==-red[j][t] for t in range(k)): return False
    return True
best=0; nodes=0; hits=[]
def combos_with_new(S):
    x=S[-1]
    for T in itertools.combinations(S[:-1],k): yield T+(x,)
def formally_related(E,U):
    red=[reduce(v,E) for v in U]
    for d in deltas:
        if all(sum(d[i]*red[i][t] for i in range(k+1))==0 for t in range(k)): return True
    return False
def resolve(E,S,subs,idx):
    # yield all valid subspaces E' on which every subset in subs[idx:] is non-dissociated
    while idx<len(subs) and formally_related(E,subs[idx]): idx+=1
    if idx==len(subs):
        yield E; return
    U=subs[idx]; seen=set()
    for d in deltas:
        c=tuple(sum(d[i]*U[i][t] for i in range(k+1)) for t in range(k))
        E2=add_eq(E,c)
        if E2==E or E2 in seen: continue
        seen.add(E2)
        if len(E2)>=k: continue
        if not valid(E2,S): continue
        yield from resolve(E2,S,subs,idx+1)
def extend(S,E,start):
    global best,nodes
    nodes+=1
    if len(S)>best:
        best=len(S); print("size",best,"forms",S,"equations",[canon_row(r) for _,r in E],flush=True)
    if len(S)>=target: hits.append((tuple(S),E))
    for ci in range(start,len(cands)):
        if len(S)+(len(cands)-ci)<target: break
        x=cands[ci]; S2=S+[x]
        if not valid(E,S2): continue
        subs=list(combos_with_new(tuple(S2)))
        seenE=set()
        for E2 in resolve(E,S2,subs,0):
            if E2 in seenE: continue
            seenE.add(E2)
            extend(S2,E2,ci+1)
extend(list(units),tuple(),0)
print(f"k={k}: largest set with a dissociated {k}-subset but no dissociated {k+1}-subset found: {best}; target {target} reached: {len(hits)>0}; nodes={nodes}")
