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
    unsigned long long mask=(poolv.size()>=64)?~0ULL:((1ULL<<poolv.size())-1);
    return dfsLine(mask); }
// ---------- general subspaces ----------
static bool solve(const Sub&L,bool top);
struct Ctx { const Sub*L; bool top; vector<Co> cc; vector<Co> uc; unordered_set<string> triedW; };
static inline bool sameUpToSign(const Co&a,const Co&b,int r){ bool eq=true,ng=true; for(int t=0;t<r;t++){ if(a[t]!=b[t]) eq=false; if(a[t]!=-b[t]) ng=false; } return eq||ng; }
static bool relatedCo(const Co*us,int r){
    for(auto&d:deltas){ bool z=true; for(int t=0;t<r && z;t++){ ll a=0; for(int i=0;i<=k;i++) a+=d[i]*us[i][t]; if(a) z=false; } if(z) return true; }
    return false; }
// S holds indices: -1-i for unit i, else candidate index
static inline const Co& coOf(const Ctx&c,int id){ return id<0 ? c.uc[-1-id] : c.cc[id]; }
static inline const Vec& vecOf(int id){ return id<0 ? units[-1-id] : cands[id]; }
static bool firstUnresolved(const Ctx&c,const vector<int>&S,int x,int*U,int*T,int depth,int startI){
    int n=S.size()-1; // S.back() = y
    if(depth==k-1){ Co us[6]; for(int i=0;i<k-1;i++){ us[i]=coOf(c,S[T[i]]); U[i]=S[T[i]]; } us[k-1]=coOf(c,S[n]); U[k-1]=S[n]; us[k]=coOf(c,x); U[k]=x;
        return !relatedCo(us,c.L->r); }
    for(int i=startI;i<n;i++){ T[depth]=i; if(firstUnresolved(c,S,x,U,T,depth+1,i+1)) return true; }
    return false; }
static bool dfs(Ctx&c,vector<int>&S,const vector<int>&list,int depth){
    nodes++;
    if((int)S.size()>best){ best=S.size(); bestVals.clear(); bestDesc="generic point of a subspace of dimension "+to_string(c.L->r)+" basis "+key(*c.L)+" forms:"; for(int id:S){ const Vec&v=vecOf(id); bestDesc+=" ("; for(int j=0;j<k;j++) bestDesc+=to_string(v[j])+(j<k-1?",":""); bestDesc+=")"; } }
    if((int)S.size()>=target) return true;
    for(size_t i=0;i<list.size();i++){
        if((int)S.size()+(int)(list.size()-i)<target) break;
        int y=list[i];
        if(c.top && caseMode && depth==0 && !startOK0[y]) continue;
        if(c.top && caseMode && depth==1 && !startOK1[y]) continue;
        S.push_back(y); vector<int> nl;
        if((int)S.size()>best){ best=S.size(); bestVals.clear(); bestDesc="generic point of a subspace of dimension "+to_string(c.L->r)+" basis "+key(*c.L)+" forms:"; for(int id:S){ const Vec&v=vecOf(id); bestDesc+=" ("; for(int j=0;j<k;j++) bestDesc+=to_string(v[j])+(j<k-1?",":""); bestDesc+=")"; } }
        for(size_t j=i+1;j<list.size();j++){ int x=list[j];
            if(sameUpToSign(c.cc[x],c.cc[y],c.L->r)) continue;      // x and y would be the same number
            int U[6],T[6];
            if(!firstUnresolved(c,S,x,U,T,0,0)){ nl.push_back(x); continue; }
            // x is not identically compatible: a configuration containing U must have b on one of these subspaces
            for(auto&d:deltas){ Vec cv{}; for(int t=0;t<=k;t++) if(d[t]){ const Vec&v=vecOf(U[t]); for(int q=0;q<k;q++) cv[q]+=d[t]*v[q]; }
                Co w=coords(*c.L,cv); ll g=0; for(int t=0;t<c.L->r;t++) g=gcdll(g,w[t]); if(g==0) continue;
                int sg=0; for(int t=0;t<c.L->r;t++) if(w[t]){ sg=w[t]>0?1:-1; break; }
                string wk; for(int t=0;t<c.L->r;t++){ wk+=to_string(sg*w[t]/g); wk+=','; }
                if(!c.triedW.insert(wk).second) continue;
                Sub L2; if(!restrictW(*c.L,w,L2) || L2.r==0) continue;
                if(solve(L2,false)) return true; }
        }
        if((int)S.size()+(int)nl.size()>=target && dfs(c,S,nl,depth+1)) return true;
        S.pop_back();
        if(c.top && depth<=1){ fprintf(stderr,"top-level: finished depth-%d choice %d  (nodes %lld, subspaces solved %lld, best %d)\n",depth,y,nodes,solves,best); }
    }
    return false; }
static bool solve(const Sub&L,bool top){
    string ky; if(!top){ ky=key(L); auto it=cacheRes.find(ky); if(it!=cacheRes.end()) return it->second; }
    solves++; bool res=false; static ll byDim[6]={0}; byDim[L.r]++; if(solves%200000==0) fprintf(stderr,"progress: solved %lld (lines %lld, planes %lld, 3-spaces %lld) nodes=%lld cpu=%.0fs\n",solves,byDim[1],byDim[2],byDim[3],nodes,(double)clock()/CLOCKS_PER_SEC);
    if(validB(L)){
        if(L.r==1) res=solveLine(L);
        else { Ctx c; c.L=&L; c.top=top; for(auto&v:cands) c.cc.push_back(coords(L,v)); for(auto&v:units) c.uc.push_back(coords(L,v));
            vector<int> S; for(int i=0;i<k;i++) S.push_back(-1-i);
            vector<int> list; for(int x=0;x<(int)cands.size();x++){ if(top && caseMode && !topAllowed[x]) continue; bool dup=false; for(int i=0;i<k;i++) if(sameUpToSign(c.cc[x],c.uc[i],L.r)) dup=true; if(!dup) list.push_back(x); }
            res=dfs(c,S,list,0); } }
    if(!top && !res) cacheRes[ky]=false;
    return res; }
int main(int argc,char**argv){ k=atoi(argv[1]); target=atoi(argv[2]); caseMode=argc>3?atoi(argv[3]):0;
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
    printf("best: %s",bestDesc.c_str()); for(ll v:bestVals) printf(" %lld",v); printf("\n"); return 0; }
