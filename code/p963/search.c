// Erdos 963: find largest set of positive integers in [1,M] with NO dissociated k-subset.
// (dissociated = all 2^k subset sums distinct)
// Backtracking; property is hereditary. Reports max size found and example sets.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int k, M, best=0, target;
int S[64], sz=0;
long nodes=0;
static int dissociated(const int *b, int kk){
    // all subset sums distinct?
    int sums[1<<6]; int ns=1<<kk; sums[0]=0;
    for(int m=1;m<ns;m++){int lb=__builtin_ctz(m); sums[m]=sums[m&(m-1)]+b[lb];}
    // check distinct: simple O(4^k) fine for k<=6
    for(int i=0;i<ns;i++)for(int j=i+1;j<ns;j++) if(sums[i]==sums[j]) return 0;
    return 1;
}
// does adding x create a dissociated k-subset? enumerate (k-1)-subsets of S[0..sz)
static int bad_rec(int *b, int depth, int start, int x){
    if(depth==k-1){ b[k-1]=x; return dissociated(b,k); }
    for(int i=start;i<sz;i++){ b[depth]=S[i]; if(bad_rec(b,depth+1,i+1,x)) return 1; }
    return 0;
}
static void rec(int next){
    nodes++;
    if(sz>best){best=sz; printf("size %d:",sz); for(int i=0;i<sz;i++)printf(" %d",S[i]); printf("\n"); fflush(stdout);}
    else if(sz==best && sz>=target){printf("size %d:",sz); for(int i=0;i<sz;i++)printf(" %d",S[i]); printf("\n");}
    for(int x=next;x<=M;x++){
        int b[8];
        if(sz>=k-1 && bad_rec(b,0,0,x)) continue;
        S[sz++]=x; rec(x+1); sz--;
    }
}
int main(int argc,char**argv){ k=atoi(argv[1]); M=atoi(argv[2]); target=argc>3?atoi(argv[3]):99; rec(1); printf("k=%d M=%d max size=%d nodes=%ld\n",k,M,best,nodes); return 0; }
