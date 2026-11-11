// Erdos 963 search v2: sets of positive integers in [1,M] with no dissociated k-subset.
// Candidate-list backtracking with bound pruning: only explores branches that can reach `target` size.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int k, M, target, best=0;
int S[64], sz=0; long nodes=0, found=0;
static inline int dissociated(const int *b){
    int sums[64]; int ns=1<<k; sums[0]=0;
    for(int m=1;m<ns;m++){int lb=__builtin_ctz(m); sums[m]=sums[m&(m-1)]+b[lb];}
    for(int i=1;i<ns;i++)for(int j=0;j<i;j++) if(sums[i]==sums[j]) return 0;
    return 1;
}
// check k-subsets consisting of x, y(=S[sz-1]) and (k-2) elements of S[0..sz-1)
static int bad_rec(int *b, int depth, int start){
    if(depth==k-2) return dissociated(b);
    for(int i=start;i<sz-1;i++){ b[depth]=S[i]; if(bad_rec(b,depth+1,i+1)) return 1; }
    return 0;
}
static void rec(int *cand, int nc){
    nodes++;
    if(sz>best){best=sz; printf("size %d:",sz); for(int i=0;i<sz;i++)printf(" %d",S[i]); printf("\n"); fflush(stdout);}
    if(sz>=target){found++; if(sz>best||found<50){printf("HIT size %d:",sz); for(int i=0;i<sz;i++)printf(" %d",S[i]); printf("\n"); fflush(stdout);} }
    int *nc2=malloc(sizeof(int)*(nc+1));
    for(int i=0;i<nc;i++){
        if(sz+(nc-i)<target) break;
        int y=cand[i];
        S[sz++]=y;
        int n2=0;
        for(int j=i+1;j<nc;j++){
            int x=cand[j]; int b[8]; b[k-1]=x; b[k-2]=y;
            if(sz-1>=k-2 && bad_rec(b,0,0)) continue;
            nc2[n2++]=x;
        }
        if(sz+n2>=target || sz>=best) rec(nc2,n2);
        sz--;
    }
    free(nc2);
}
int main(int argc,char**argv){ k=atoi(argv[1]); M=atoi(argv[2]); target=atoi(argv[3]);
    int *c=malloc(sizeof(int)*M); for(int i=0;i<M;i++)c[i]=i+1; rec(c,M);
    printf("k=%d M=%d target=%d best=%d hits=%ld nodes=%ld\n",k,M,target,best,found,nodes); return 0; }
