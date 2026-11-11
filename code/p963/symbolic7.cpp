// Erdos 963: exhaustive symbolic search over ALL real sets with a maximal dissociated subset B of size k.
// Every element of such a set S is +-(eps.b), eps in {-1,0,1}^k (b = values of B).  b ranges over R^k; the
// search branches exhaustively on which {-1,0,1}-relation makes each (k+1)-subset non-dissociated, each such
// relation being a linear equation on b.  L = current linear subspace containing b, stored as a canonical
// integer RREF basis (r rows).  A form v vanishes identically on L iff v.row_i = 0 for all i.
// Output: whether a set of size >= target with no dissociated (k+1)-subset exists.
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int k, target; 
typedef array<ll,5> Vec;            // length k
struct Sub { int r; Vec rows[5]; }; // canonical RREF basis of L
static ll gcdll(ll a, ll b){ a=llabs(a); b=llabs(b); while(b){ll t=a%b;a=b;b=t;} return a; }
static void prim(Vec&v){ ll g=0; for(int j=0;j<k;j++) g=gcdll(g,v[j]); if(g>1) for(int j=0;j<k;j++) v[j]/=g; }
static void canon(Sub&s){ // integer fraction-free RREF
    int row=0;
    for(int col=0; col<k && row<s.r; col++){
        int p=-1; for(int i=row;i<s.r;i++) if(s.rows[i][col]!=0){p=i;break;}
        if(p<0) continue; swap(s.rows[row],s.rows[p]);
        if(s.rows[row][col]<0) for(int j=0;j<k;j++) s.rows[row][j]=-s.rows[row][j];
        for(int i=0;i<s.r;i++) if(i!=row && s.rows[i][col]!=0){
            ll a=s.rows[row][col], c=s.rows[i][col];
            for(int j=0;j<k;j++) s.rows[i][j]=s.rows[i][j]*a-c*s.rows[row][j];
            prim(s.rows[i]);
        }
        prim(s.rows[row]); row++;
    }
    // drop zero rows
    int r2=0; for(int i=0;i<s.r;i++){ bool z=true; for(int j=0;j<k;j++) if(s.rows[i][j]) z=false; if(!z) s.rows[r2++]=s.rows[i]; }
    s.r=r2;
    for(int i=0;i<s.r;i++){ // make pivot positive & primitive
        prim(s.rows[i]); for(int j=0;j<k;j++) if(s.rows[i][j]){ if(s.rows[i][j]<0) for(int t=0;t<k;t++) s.rows[i][t]=-s.rows[i][t]; break; }
    }
}
static string key(const Sub&s){ string o; for(int i=0;i<s.r;i++){ for(int j=0;j<k;j++){ o+=to_string(s.rows[i][j]); o+=','; } o+=';'; } return o; }
typedef array<ll,5> Co; // coordinates of a form on L (length r)
static inline Co coords(const Sub&s,const Vec&v){ Co u{}; for(int i=0;i<s.r;i++){ ll t=0; for(int j=0;j<k;j++) t+=v[j]*s.rows[i][j]; u[i]=t; } return u; }
static bool restrictSub(const Sub&s,const Vec&c,Sub&out){ // L' = L ∩ {c.b=0}; false if c vanishes on L (no change)
    Co w=coords(s,c); int p=-1; for(int i=0;i<s.r;i++) if(w[i]){p=i;break;} if(p<0) return false;
    out.r=0;
    for(int i=0;i<s.r;i++) if(i!=p){ Vec nr; for(int j=0;j<k;j++) nr[j]=w[p]*s.rows[i][j]-w[i]*s.rows[p][j]; prim(nr); out.rows[out.r++]=nr; }
    canon(out); return true;
}
vector<Vec> half, cands, units; vector<array<int,6>> deltas;
static bool validSub(const Sub&s,const vector<Vec>&S){
    if(s.r==0) return false;
    for(auto&e:half){ Co u=coords(s,e); bool z=true; for(int i=0;i<s.r;i++) if(u[i]){z=false;break;} if(z) return false; }
    vector<Co> cs; cs.reserve(S.size()); for(auto&v:S) cs.push_back(coords(s,v));
    for(size_t i=0;i<cs.size();i++) for(size_t j=0;j<i;j++){
        bool eq=true, ng=true; for(int t=0;t<s.r;t++){ if(cs[i][t]!=cs[j][t]) eq=false; if(cs[i][t]!=-cs[j][t]) ng=false; }
        if(eq||ng) return false; }
    return true;
}
static bool related(const Sub&s,const Co*us){ // exists delta with sum delta_i u_i = 0 ?
    for(auto&d:deltas){ bool z=true; for(int t=0;t<s.r && z;t++){ ll a=0; for(int i=0;i<=k;i++) a+=d[i]*us[i][t]; if(a) z=false; } if(z) return true; }
    return false;
}
struct PH{ size_t operator()(const pair<ll,ll>&p) const { return hash<ll>()(p.first*1000003LL+p.second); } };
unordered_set<pair<ll,ll>,PH> *planeTested=nullptr;
unordered_map<string,bool> lineRes, subRes;
static bool lineResult(const Sub&s);
ll nodes=0; int best=0; bool hit=false; vector<Vec> bestS; Sub bestL;
static void resolve(const Sub&s,const vector<Vec>&S,const vector<array<int,6>>&subs,size_t idx,vector<Sub>&out,unordered_set<string>&seenOut){
    Co us[6];
    while(idx<subs.size()){
        for(int i=0;i<=k;i++) us[i]=coords(s,S[subs[idx][i]]);
        if(related(s,us)) idx++; else break;
    }
    if(idx==subs.size()){ string ky=key(s); if(seenOut.insert(ky).second) out.push_back(s); return; }
    unordered_set<string> seen;
    for(auto&d:deltas){
        Vec c{}; for(int i=0;i<=k;i++) if(d[i]) for(int j=0;j<k;j++) c[j]+=d[i]*S[subs[idx][i]][j];
        if(s.r==2){ // children are lines: decide by the per-line cache, never recurse
            Co w=coords(s,c); if(w[0]==0&&w[1]==0) continue; ll g=gcdll(w[0],w[1]); ll a=w[0]/g,b=w[1]/g; if(a<0||(a==0&&b<0)){a=-a;b=-b;}
            if(planeTested){ if(!planeTested->insert({a,b}).second) continue; }
            Sub s2; if(!restrictSub(s,c,s2)) continue; if(s2.r==0) continue;
            if(lineResult(s2)){ hit=true; return; }
            continue; }
        Sub s2; if(!restrictSub(s,c,s2)) continue;
        if(s2.r==0) continue;
        string ky=key(s2); if(!seen.insert(ky).second) continue;
        if(s2.r>1 && subRes.count(ky)) continue;
        if(!validSub(s2,S)) continue;
        resolve(s2,S,subs,idx+1,out,seenOut); if(hit) return;
    }
}

// ---- fast finishing routine once L is a line (dim 1): all forms are concrete integers ----
static inline bool diss5(const ll*v){ // k+1 values: all 2^(k+1) subset sums distinct?
    int m=k+1, ns=1<<m; ll sums[64]; sums[0]=0;
    for(int t=1;t<ns;t++){ int lb=__builtin_ctz(t); sums[t]=sums[t&(t-1)]+v[lb]; }
    sort(sums,sums+ns); for(int t=1;t<ns;t++) if(sums[t]==sums[t-1]) return false; return true;
}
static vector<ll> curv; ll dim1calls=0;
// does adding x (with y just added as last element of curv) create a dissociated (k+1)-subset containing x and y?
static bool badXY(ll x,int choose,int startI,ll*buf,int depth){
    int n=curv.size()-1; // elements before y
    if(depth==choose){ buf[k-1]=curv[n]; buf[k]=x; return diss5(buf); }
    for(int i=startI;i<n;i++){ buf[depth]=curv[i]; if(badXY(x,choose,i+1,buf,depth+1)) return true; }
    return false;
}
static bool badX(ll x,int startI,ll*buf,int depth){ // any k-subset of curv with x dissociated?
    int n=curv.size();
    if(depth==k){ buf[k]=x; return diss5(buf); }
    for(int i=startI;i<n;i++){ buf[depth]=curv[i]; if(badX(x,i+1,buf,depth+1)) return true; }
    return false;
}
static void dfs1(vector<ll>&pool){
    if((int)curv.size()>best){ best=curv.size(); fprintf(stderr,"size %d (line) values:",best); for(ll v:curv) fprintf(stderr," %lld",v); fprintf(stderr,"\n"); }
    if((int)curv.size()>=target){ hit=true; return; }
    for(size_t i=0;i<pool.size();i++){
        if((int)curv.size()+(int)(pool.size()-i)<target) break;
        ll y=pool[i]; curv.push_back(y);
        vector<ll> np; ll buf[8];
        for(size_t j=i+1;j<pool.size();j++){ if(!badXY(pool[j],k-1,0,buf,0)) np.push_back(pool[j]); }
        if((int)curv.size()+(int)np.size()>=target) dfs1(np);
        curv.pop_back(); if(hit) return;
    }
}
static void finishDim1(const vector<Vec>&S,const Sub&s,int start){
    dim1calls++;
    curv.clear(); for(auto&v:S){ ll t=0; for(int j=0;j<k;j++) t+=v[j]*s.rows[0][j]; curv.push_back(llabs(t)); }
    set<ll> have(curv.begin(),curv.end()); vector<ll> pool; ll buf[8];
    for(int ci=start; ci<(int)cands.size(); ci++){ ll t=0; for(int j=0;j<k;j++) t+=cands[ci][j]*s.rows[0][j]; t=llabs(t);
        if(t==0||have.count(t)) continue; have.insert(t);
        if(!badX(t,0,buf,0)) pool.push_back(t); }
    if((int)curv.size()+(int)pool.size()>=target) dfs1(pool);
}
vector<char> startOK0, startOK1; int caseMode=0; ll nodesByDim[6]={0}; int pathci[64]; 

static bool lineResult(const Sub&s){ // is there ANY valid set of size >= target with b on this line?
    string ky=key(s); auto it=lineRes.find(ky); if(it!=lineRes.end()) return it->second;
    bool res=false;
    if(validSub(s,units)){ bool before=hit; finishDim1(units,s,0); res=hit; if(!before && res) return true; }
    lineRes[ky]=res; return res;
}
static void extend(vector<Vec>&S,const Sub&s,int start,const string*freshKey){
    nodes++; int depth=(int)S.size()-k; nodesByDim[s.r]++; if((nodes&((1LL<<16)-1))==0){ fprintf(stderr,"nodes=%lld dims[1..4]=%lld %lld %lld %lld dim1calls=%lld path:",nodes,nodesByDim[1],nodesByDim[2],nodesByDim[3],nodesByDim[4],dim1calls); for(int i=0;i<depth&&i<6;i++) fprintf(stderr," %d",pathci[i]); fprintf(stderr,"\n"); }
    if((int)S.size()>best){ best=S.size(); bestS=S; bestL=s; fprintf(stderr,"size %d (dim %d) nodes %lld\n",best,s.r,nodes); }
    if((int)S.size()>=target){ hit=true; return; }
    if(s.r>1 && s.r<k){ string ky=key(s);
        if(!freshKey || *freshKey!=ky){
            if(subRes.count(ky)) return;            // known: no configuration with b in this subspace reaches target
            vector<Vec> S0=units; unordered_set<pair<ll,ll>,PH> tested; auto saved=planeTested; planeTested=(s.r==2)?&tested:nullptr;
            extend(S0,s,0,&ky); planeTested=saved; if(hit) return; subRes[ky]=false; return; } }
    if(s.r==1){ if(lineResult(s)) hit=true; return; }
    for(int ci=start; ci<(int)cands.size(); ci++){
        if((int)S.size()+((int)cands.size()-ci)<target) break;
        if(caseMode && !freshKey && depth==0 && !startOK0[ci]) continue;
        if(caseMode && !freshKey && depth==1 && !startOK1[ci]) continue;
        S.push_back(cands[ci]); pathci[depth]=ci;
        if(validSub(s,S)){
            // all (k+1)-subsets containing the new element
            vector<array<int,6>> subs; int n=S.size()-1; vector<int> idx(k);
            function<void(int,int)> rec=[&](int d,int st){ if(d==k){ array<int,6> a{}; for(int i=0;i<k;i++)a[i]=idx[i]; a[k]=n; subs.push_back(a); return;} for(int i=st;i<n;i++){idx[d]=i;rec(d+1,i+1);} };
            rec(0,0);
            vector<Sub> outs; unordered_set<string> seenOut; resolve(s,S,subs,0,outs,seenOut); if(hit){ S.pop_back(); return; }
            for(auto&s2:outs){ extend(S,s2,ci+1,freshKey); if(hit) { S.pop_back(); return; } }
        }
        S.pop_back();
        if(caseMode && !freshKey && depth==1) fprintf(stderr,"done depth-1 branch ci=%d nodes=%lld best=%d\n",ci,nodes,best);
    }
}
int main(int argc,char**argv){ k=atoi(argv[1]); target=atoi(argv[2]);
    int tot=1; for(int i=0;i<k;i++) tot*=3;
    for(int m=0;m<tot;m++){ Vec e{}; int x=m; bool any=false; for(int j=0;j<k;j++){ e[j]=x%3-1; x/=3; if(e[j]) any=true; } if(!any) continue;
        int first=0; for(int j=0;j<k;j++) if(e[j]){first=e[j];break;} if(first<0) continue; half.push_back(e);
        int nz=0; for(int j=0;j<k;j++) if(e[j]) nz++; if(nz==1) continue; cands.push_back(e); }
    for(int i=0;i<k;i++){ Vec u{}; u[i]=1; units.push_back(u); }
    int totd=tot*3; for(int m=0;m<totd;m++){ array<int,6> d{}; int x=m; bool any=false; for(int j=0;j<=k;j++){ d[j]=x%3-1; x/=3; if(d[j]) any=true; } if(!any) continue;
        int first=0; for(int j=0;j<=k;j++) if(d[j]){first=d[j];break;} if(first<0) continue; deltas.push_back(d); }
    caseMode = argc>3 ? atoi(argv[3]) : 0;
    if(caseMode){ // k=4 symmetry reduction. caseMode 1: S contains e1+e2.  caseMode 2: no weight-2 forms, contains e1+e2+e3.
        auto wt=[&](const Vec&e){int n=0;for(int j=0;j<k;j++) if(e[j]) n++; return n;};
        auto blockA=[&](const Vec&e)->int{ int w=wt(e); bool s12=(e[0]!=0&&e[1]!=0); bool same=(e[0]==e[1]);
            if(w==2){ if(s12) return same?0:1; if(e[0]==0&&e[1]==0) return 2; return 3; }
            if(w==3){ if(s12) return same?4:5; return 6; }
            return same?7:8; };
        vector<Vec> nc; vector<int> blk;
        if(caseMode==1){ for(int b=0;b<=8;b++) for(auto&e:cands) if(blockA(e)==b){ nc.push_back(e); blk.push_back(b);} }
        else { Vec r{}; r[0]=r[1]=r[2]=1; nc.push_back(r); blk.push_back(0); for(int w=3;w<=4;w++) for(auto&e:cands) if(wt(e)==w && !(e==r)){ nc.push_back(e); blk.push_back(1);} }
        cands=nc; startOK0.assign(cands.size(),0); startOK1.assign(cands.size(),1); startOK0[0]=1;
        if(caseMode==1){ for(size_t i=1;i<cands.size();i++) startOK1[i]=(blk[i]!=blk[i-1]); }
        fprintf(stderr,"case %d: %zu candidates\n",caseMode,cands.size());
    }
    Sub full; full.r=k; for(int i=0;i<k;i++){ full.rows[i]=Vec{}; full.rows[i][i]=1; }
    vector<Vec> S=units; extend(S,full,0,nullptr);
    printf("k=%d target=%d case=%d: reached=%s best=%d nodes=%lld lines=%zu subspaces=%zu\n",k,target,caseMode,hit?"YES":"NO",best,nodes,lineRes.size(),subRes.size());
    printf("best set forms:"); for(auto&v:bestS){ printf(" ("); for(int j=0;j<k;j++) printf("%lld%s",v[j],j<k-1?",":""); printf(")"); } printf("\nbest L basis:");
    for(int i=0;i<bestL.r;i++){ printf(" ["); for(int j=0;j<k;j++) printf("%lld%s",bestL.rows[i][j],j<k-1?",":""); printf("]"); } printf("\n");
    return 0; }
