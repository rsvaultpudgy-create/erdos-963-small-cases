// Erdos 963 — exhaustive symbolic search, final version ("flat" recursion with caching).
// Claim tested: there is NO set S of nonzero reals (no two equal or opposite) whose largest dissociated subset has
// exactly k elements and |S| >= target.
// Setup: B = a dissociated k-subset with values b in R^k.  Every other element is +-(eps.b), eps in {-1,0,1}^k.
// A (k+1)-subset is non-dissociated iff some delta in {-1,0,1}^(k+1) gives a vanishing combination = a linear equation c.b=0.
// solve(L) decides: does a configuration of size >= target exist with b in the subspace L?
//   - sets whose relations all hold identically on L are found by a candidate-list DFS on L;
//   - whenever a candidate x is not identically compatible, every proper subspace L∩{c.b=0} coming from one
//     unresolved subset is solved recursively (a real configuration containing that subset must lie in one of them).
// Subspaces are stored as canonical integer RREF bases and cached.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int k, target, caseMode=0;
typedef array<ll,5> Vec; typedef array<ll,5> Co;
struct Sub { int r; Vec rows[5]; };
static ll gcdll(ll a, ll b){ a=llabs(a); b=llabs(b); while(b){ll t=a%b;a=b;b=t;} return a; }
static void prim(Vec&v){ ll g=0; for(int j=0;j<k;j++) g=gcdll(g,v[j]); if(g>1) for(int j=0;j<k;j++) v[j]/=g; }
static void canon(Sub&s){
    int row=0;
    for(int col=0; col<k && row<s.r; col++){
        int p=-1; for(int i=row;i<s.r;i++) if(s.rows[i][col]!=0){p=i;break;}
        if(p<0) continue; swap(s.rows[row],s.rows[p]);
        for(int i=0;i<s.r;i++) if(i!=row && s.rows[i][col]!=0){
            ll a=s.rows[row][col], c=s.rows[i][col];
            for(int j=0;j<k;j++) s.rows[i][j]=s.rows[i][j]*a-c*s.rows[row][j];
            prim(s.rows[i]); }
        prim(s.rows[row]); row++; }
    int r2=0; for(int i=0;i<s.r;i++){ bool z=true; for(int j=0;j<k;j++) if(s.rows[i][j]) z=false; if(!z) s.rows[r2++]=s.rows[i]; }
    s.r=r2;
    for(int i=0;i<s.r;i++){ prim(s.rows[i]); for(int j=0;j<k;j++) if(s.rows[i][j]){ if(s.rows[i][j]<0) for(int t=0;t<k;t++) s.rows[i][t]=-s.rows[i][t]; break; } }
}
static string key(const Sub&s){ string o; for(int i=0;i<s.r;i++){ for(int j=0;j<k;j++){ o+=to_string(s.rows[i][j]); o+=','; } o+=';'; } return o; }
static inline Co coords(const Sub&s,const Vec&v){ Co u{}; for(int i=0;i<s.r;i++){ ll t=0; for(int j=0;j<k;j++) t+=v[j]*s.rows[i][j]; u[i]=t; } return u; }
static bool restrictW(const Sub&s,const Co&w,Sub&out){
    int p=-1; for(int i=0;i<s.r;i++) if(w[i]){p=i;break;} if(p<0) return false;
    out.r=0; for(int i=0;i<s.r;i++) if(i!=p){ Vec nr; for(int j=0;j<k;j++) nr[j]=w[p]*s.rows[i][j]-w[i]*s.rows[p][j]; prim(nr); out.rows[out.r++]=nr; }
    canon(out); return true; }
vector<Vec> half, cands, units; vector<array<int,6>> deltas; vector<char> startOK0, startOK1, topAllowed;
int best=0; ll nodes=0, solves=0; vector<ll> bestVals; string bestDesc;
unordered_map<string,bool> cacheRes;
static bool validB(const Sub&s){ if(s.r==0) return false;
    for(auto&e:half){ Co u=coords(s,e); bool z=true; for(int i=0;i<s.r;i++) if(u[i]){z=false;break;} if(z) return false; } return true; }
// ---------- lines: concrete integers ----------
static inline bool dissInt(const ll*v){ int m=k+1, ns=1<<m; ll sums[64]; sums[0]=0;
    for(int t=1;t<ns;t++){ int lb=__builtin_ctz(t); sums[t]=sums[t&(t-1)]+v[lb]; }
    sort(sums,sums+ns); for(int t=1;t<ns;t++) if(sums[t]==sums[t-1]) return false; return true; }
static vector<ll> curv; static vector<ll> poolv; // poolv sorted
static ll lemmaM=0, shortcutLines=0, fullLines=0;
static inline int poolIndex(ll v){ auto it=lower_bound(poolv.begin(),poolv.end(),v); if(it!=poolv.end() && *it==v) return it-poolv.begin(); return -1; }
// A (k+1)-set Q+{x} with Q a dissociated k-set is non-dissociated iff x = |sum eps_i q_i| for some signs eps.
// So after choosing y, the allowed pool shrinks to the intersection of the signed-sum sets of all dissociated k-sets Q containing y.
static bool shrinkRec(unsigned long long&mask,ll*q,int depth,int startI,int need){
    int n=curv.size()-1;
    if(depth==k-1){ q[k-1]=curv[n];
        int tot=1; for(int i=0;i<k;i++) tot*=3; unsigned long long ss=0;
        for(int m=0;m<tot;m++){ int x=m; ll v=0; bool any=false; for(int i=0;i<k;i++){ int e=x%3-1; x/=3; if(e){ any=true; v+=e*q[i]; } }
            if(!any) continue; if(v==0) return true;          // Q itself is not dissociated: no restriction from Q
            if(v>0){ int id=poolIndex(v); if(id>=0) ss|=1ULL<<id; } }
        mask&=ss; return __builtin_popcountll(mask)>=need; }
    for(int i=startI;i<n;i++){ q[depth]=curv[i]; if(!shrinkRec(mask,q,depth+1,i+1,need)) return false; }
    return true; }
static bool dfsLine(unsigned long long mask){
    if((int)curv.size()>=target) return true;
    while(mask){
        if((int)curv.size()+__builtin_popcountll(mask)<target) break;
        int i=__builtin_ctzll(mask); mask&=mask-1;
        curv.push_back(poolv[i]);
        if((int)curv.size()>best){ best=curv.size(); bestVals=curv; bestDesc="integers"; }
        unsigned long long nm=mask; ll q[8]; int need=target-(int)curv.size();
        if(shrinkRec(nm,q,0,0,need) && dfsLine(nm)) return true;
        if((int)curv.size()>=target) return true;
        curv.pop_back(); }
    return false; }
static bool solveLine(const Sub&s){
    curv.clear(); poolv.clear(); set<ll> have; for(auto&v:units){ ll t=llabs(coords(s,v)[0]); curv.push_back(t); have.insert(t); }
    for(auto&c:cands){ ll t=llabs(coords(s,c)[0]); if(t==0||have.count(t)) continue; have.insert(t); poolv.push_back(t); }
    sort(poolv.begin(),poolv.end());
    // Shortcut (k=4, target>=14 only): the separate exhaustive integer search (search2.c, run with arguments 5 130 14)
    // shows that no 14 positive integers <= 130 avoid a dissociated 5-subset.  All numbers on this line are <= sum|b_i|.
    if(k==4 && target>=14 && lemmaM>0){ ll mx=0; for(ll v:curv) mx=max(mx,v); for(ll v:poolv) mx=max(mx,v); if(mx<=lemmaM){ shortcutLines++; return false; } }
    fullLines++;
    unsigned long long mask=(poolv.size()>=64)?~0ULL:((1ULL<<poolv.size())-1);
    return dfsLine(mask); }
// ---------- general subspaces ----------
static bool solve(const Sub&L,bool top);
typedef unsigned long long u64;
struct SmallMap { u64 keys[256]; u64 vals[256]; bool used[256]; SmallMap(){ memset(used,0,sizeof(used)); }
    static inline unsigned h(u64 k){ k^=k>>29; k*=0x9E3779B97F4A7C15ULL; return (unsigned)(k>>56); }
    inline u64& operator[](u64 k){ unsigned i=h(k); while(used[i] && keys[i]!=k) i=(i+1)&255; if(!used[i]){ used[i]=true; keys[i]=k; vals[i]=0; } return vals[i]; }
    inline u64 get(u64 k) const { unsigned i=h(k); while(used[i]){ if(keys[i]==k) return vals[i]; i=(i+1)&255; } return 0; } };
struct Ctx { const Sub*L; bool top; int r; vector<Co> cc; vector<Co> uc; SmallMap H; unordered_set<u64> triedW, triedU; };
static inline u64 packCo(const Co&w,int r){ // sign-normalised packing (first nonzero coordinate positive)
    int sg=0; for(int t=0;t<r;t++) if(w[t]){ sg=w[t]>0?1:-1; break; }
    u64 key=0; for(int t=0;t<r;t++){ ll v=sg*w[t]; if(v<-(1LL<<19)||v>(1LL<<19)){ fprintf(stderr,"coordinate overflow\n"); exit(2);} key|=(u64)(v+(1LL<<20))<<(21*t); } return key; }
static inline const Co& coOf(const Ctx&c,int id){ return id<0 ? c.uc[-1-id] : c.cc[id]; }
static bool dfs(Ctx&c,vector<int>&S,u64 mask,int depth){
    nodes++; int r=c.r;
    if((int)S.size()>=target) return true;
    while(mask){
        if((int)S.size()+__builtin_popcountll(mask)<target) break;
        int y=__builtin_ctzll(mask); mask&=mask-1;
        if(c.top && caseMode && depth==0 && !startOK0[y]) continue;
        if(c.top && caseMode && depth==1 && !startOK1[y]) continue;
        int n=S.size(); S.push_back(y);
        if((int)S.size()>best){ best=S.size(); bestVals.clear(); bestDesc="generic point of a subspace of dimension "+to_string(r)+", basis "+key(*c.L)+" forms:"; for(int id:S){ const Vec&v=id<0?units[-1-id]:cands[id]; bestDesc+=" ("; for(int q=0;q<k;q++) bestDesc+=to_string(v[q])+(q<k-1?",":""); bestDesc+=")"; } }
        u64 nm=mask & ~c.H.get(packCo(c.cc[y],r));                // forms equal to +-y on L are the same number
        // every k-subset Q = T+{y}, T a (k-1)-subset of the earlier elements
        int T[6]; for(int t=0;t<k-1;t++) T[t]=t;
        bool more=(n>=k-1);
        while(more){
            Co q[6]; for(int t=0;t<k-1;t++) q[t]=coOf(c,S[T[t]]); q[k-1]=c.cc[y];
            int tot=1; for(int t=0;t<k;t++) tot*=3; u64 ss=0; bool related=false;
            for(int m=1;m<tot && !related;m++){ int x=m; Co v{}; int lead=0;
                for(int t=0;t<k;t++){ int e=x%3; x/=3; if(e==2) e=-1; if(e){ if(!lead) lead=e; for(int u=0;u<r;u++) v[u]+=e*q[t][u]; } }
                if(lead<0) continue;                                   // each +-pair once
                bool z=true; for(int u=0;u<r;u++) if(v[u]){z=false;break;}
                if(z){ related=true; break; }
                ss|=c.H.get(packCo(v,r)); }
            if(!related){
                u64 dropped=nm & ~ss;
                while(dropped){ int x=__builtin_ctzll(dropped); dropped&=dropped-1;
                    // U = Q+{x} is not identically non-dissociated: any real configuration containing U has b on a proper subspace
                    int ids[6]; for(int t=0;t<k-1;t++) ids[t]=S[T[t]]+8; ids[k-1]=y+8; ids[k]=x+8; sort(ids,ids+k+1);
                    u64 uk=0; for(int t=0;t<=k;t++) uk=uk*64+ids[t];
                    if(!c.triedU.insert(uk).second) continue;
                    Co us[6]; for(int t=0;t<k;t++) us[t]=q[t]; us[k]=c.cc[x];
                    for(auto&d:deltas){ Co w{}; for(int t=0;t<=k;t++) if(d[t]) for(int u=0;u<r;u++) w[u]+=d[t]*us[t][u];
                        ll g=0; for(int u=0;u<r;u++) g=gcdll(g,w[u]); if(g==0) continue; for(int u=0;u<r;u++) w[u]/=g;
                        if(!c.triedW.insert(packCo(w,r)).second) continue;
                        Sub L2; if(!restrictW(*c.L,w,L2) || L2.r==0) continue;
                        if(solve(L2,false)) return true; } }
                nm&=ss; }
            // next (k-1)-combination of {0..n-1}
            int t=k-2; while(t>=0 && T[t]==n-(k-1)+t) t--; if(t<0) more=false; else { T[t]++; for(int u=t+1;u<k-1;u++) T[u]=T[u-1]+1; }
        }
        if((int)S.size()+__builtin_popcountll(nm)>=target && dfs(c,S,nm,depth+1)) return true;
        S.pop_back();
        if(c.top && depth<=1){ fprintf(stderr,"top-level: finished depth-%d choice %d  (nodes %lld, subspaces solved %lld, best %d, cpu %.0fs)\n",depth,y,nodes,solves,best,(double)clock()/CLOCKS_PER_SEC); }
    }
    return false; }
static bool solve(const Sub&L,bool top){
    string ky; if(!top){ ky=key(L); auto it=cacheRes.find(ky); if(it!=cacheRes.end()) return it->second; }
    solves++; bool res=false; static ll byDim[6]={0}; byDim[L.r]++; if(solves%500000==0) fprintf(stderr,"progress: solved %lld (lines %lld, planes %lld, 3-spaces %lld) nodes=%lld lines by shortcut %lld / full %lld cpu=%.0fs\n",solves,byDim[1],byDim[2],byDim[3],nodes,shortcutLines,fullLines,(double)clock()/CLOCKS_PER_SEC);
    if(validB(L)){
        if(L.r==1) res=solveLine(L);
        else { Ctx c; c.L=&L; c.top=top; c.r=L.r; for(auto&v:cands) c.cc.push_back(coords(L,v)); for(auto&v:units) c.uc.push_back(coords(L,v));
            u64 unitKeys[6]; for(int i=0;i<k;i++) unitKeys[i]=packCo(c.uc[i],L.r);
            u64 mask=0;
            for(int x=0;x<(int)cands.size();x++){ u64 pk=packCo(c.cc[x],L.r); c.H[pk]|=1ULL<<x;
                if(top && caseMode && !topAllowed[x]) continue; bool dup=false; for(int i=0;i<k;i++) if(pk==unitKeys[i]) dup=true; if(!dup) mask|=1ULL<<x; }
            vector<int> S; for(int i=0;i<k;i++) S.push_back(-1-i);
            res=dfs(c,S,mask,0); } }
    if(!top && !res) cacheRes[ky]=false;
    return res; }
int main(int argc,char**argv){ k=atoi(argv[1]); target=atoi(argv[2]); caseMode=argc>3?atoi(argv[3]):0; lemmaM=argc>4?atoll(argv[4]):0;
    int tot=1; for(int i=0;i<k;i++) tot*=3;
    for(int m=0;m<tot;m++){ Vec e{}; int x=m; bool any=false; for(int j=0;j<k;j++){ e[j]=x%3-1; x/=3; if(e[j]) any=true; } if(!any) continue;
        int first=0; for(int j=0;j<k;j++) if(e[j]){first=e[j];break;} if(first<0) continue; half.push_back(e);
        int nz=0; for(int j=0;j<k;j++) if(e[j]) nz++; if(nz==1) continue; cands.push_back(e); }
    for(int i=0;i<k;i++){ Vec u{}; u[i]=1; units.push_back(u); }
    int totd=tot*3; for(int m=0;m<totd;m++){ array<int,6> d{}; int x=m; bool any=false; for(int j=0;j<=k;j++){ d[j]=x%3-1; x/=3; if(d[j]) any=true; } if(!any) continue;
        int first=0; for(int j=0;j<=k;j++) if(d[j]){first=d[j];break;} if(first<0) continue; deltas.push_back(d); }
    if(caseMode){ // k=4 symmetry reduction (signed permutations of b). 1: S contains e1+e2. 2: no weight-2 forms, contains e1+e2+e3. 3: only weight-4 forms.
        auto wt=[&](const Vec&e){int n=0;for(int j=0;j<k;j++) if(e[j]) n++; return n;};
        auto blockA=[&](const Vec&e)->int{ int w=wt(e); bool s12=(e[0]!=0&&e[1]!=0); bool same=(e[0]==e[1]);
            if(w==2){ if(s12) return same?0:1; if(e[0]==0&&e[1]==0) return 2; return 3; }
            if(w==3){ if(s12) return same?4:5; return 6; } return same?7:8; };
        vector<Vec> nc; vector<int> blk; vector<char> allow;
        if(caseMode==1){ for(int b=0;b<=8;b++) for(auto&e:cands) if(blockA(e)==b){ nc.push_back(e); blk.push_back(b); allow.push_back(1);} }
        else { Vec r{}; r[0]=r[1]=r[2]=1; nc.push_back(r); blk.push_back(0); allow.push_back(1);
               for(int w=3;w<=4;w++) for(auto&e:cands) if(wt(e)==w && !(e==r)){ nc.push_back(e); blk.push_back(1); allow.push_back(1);}
               for(auto&e:cands) if(wt(e)==2){ nc.push_back(e); blk.push_back(2); allow.push_back(0);} }   // weight-2 forms: sub-problems only
        cands=nc; topAllowed=allow; startOK0.assign(cands.size(),0); startOK1.assign(cands.size(),1); startOK0[0]=1;
        if(caseMode==1){ for(size_t i=1;i<cands.size();i++) startOK1[i]=(blk[i]!=blk[i-1]); }
        fprintf(stderr,"case %d: %zu candidate forms\n",caseMode,cands.size());
    }
    Sub fullS; fullS.r=k; for(int i=0;i<k;i++){ fullS.rows[i]=Vec{}; fullS.rows[i][i]=1; }
    bool res=solve(fullS,true);
    printf("k=%d target=%d case=%d: configuration of size >= target exists: %s | best size seen %d | nodes %lld | subspaces solved %lld\n",k,target,caseMode,res?"YES":"NO",best,nodes,solves);
    printf("lines decided by integer-range shortcut: %lld, by full search: %lld\n",shortcutLines,fullLines);
    printf("best: %s",bestDesc.c_str()); for(ll v:bestVals) printf(" %lld",v); printf("\n"); return 0; }
