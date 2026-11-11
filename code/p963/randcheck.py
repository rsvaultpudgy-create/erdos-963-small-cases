# Sanity test (not a proof): random and structured sets of positive integers.
# Checks: every 7-set has a dissociated 4-subset; every 14-set has a dissociated 5-subset.
import random, itertools
def diss(t):
    sums={0}
    for x in t:
        new={s+x for s in sums}
        if new & sums: return False
        sums|=new
    return True
def maxdiss_at_least(S,k):
    return any(diss(t) for t in itertools.combinations(S,k))
random.seed(1); bad=0; tests=0
for size,k in ((7,4),(14,5)):
    for trial in range(3000 if size==7 else 600):
        mode=trial%3
        if mode==0: S=random.sample(range(1,40),size)
        elif mode==1: S=random.sample(range(1,400),size)
        else:
            b=[random.randint(1,30) for _ in range(k-1)]
            pool=sorted({abs(sum(e*x for e,x in zip(eps,b))) for eps in itertools.product((-1,0,1),repeat=k-1)}-{0})
            if len(pool)<size: continue
            S=random.sample(pool,size)
        tests+=1
        if not maxdiss_at_least(S,k): bad+=1; print("COUNTEREXAMPLE?",size,k,sorted(S))
print("tests",tests,"failures",bad)
# the extremal examples
for S,k in (([1,2,3],3),([1,2,3,4,5,6],4),([1,2,3,4,5,6,7,8,9,10,12,13,15],5)):
    print(S,"has a dissociated",k,"-subset:",maxdiss_at_least(S,k),"| has a dissociated",k-1,"-subset:",maxdiss_at_least(S,k-1))
