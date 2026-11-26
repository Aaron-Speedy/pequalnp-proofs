#include <array>
#include <algorithm>
#include <bit>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using namespace std;
using M=unsigned;
const M full=(1u<<31)-1;
struct Box{M a=0,b=0;};
array<M,31> rows{};mt19937 gen(3701);
struct Search{
 vector<int> cell,color,degree;
 vector<vector<int>> adj;
 vector<M> used; int nodes=0,limit=2500,k;
 Search(vector<int> v,int count):cell(move(v)),k(count){
    shuffle(cell.begin(),cell.end(),gen);int n=cell.size();adj.resize(n);used.resize(n);degree.resize(n);color.assign(n,-1);
    for(int i=0;i<n;i++)for(int j=0;j<i;j++){
      int a=cell[i],b=cell[j];
      if((rows[a/31]>>(b%31)|rows[b/31]>>(a%31))&1){adj[i].push_back(j);adj[j].push_back(i);}
    }
    for(int i=0;i<n;i++)degree[i]=adj[i].size();
 }
 bool solve(int left,int seen){
    if(!left)return true;
    if(++nodes>limit)return false;
    int v=-1,score=-1;
    for(int i=0;i<(int)cell.size();i++)if(color[i]<0){
      int s=popcount(used[i])*1024+degree[i];
      if(s>score){v=i;score=s;}
    }
    M avail=((1u<<min(k,seen+1))-1)&~used[v];
    while(avail){
      int t=countr_zero(avail);M bit=1u<<t;avail-=bit;
      color[v]=t;vector<int> changed;
      bool possible=true;
      for(int u:adj[v])if(color[u]<0){
        degree[u]--;
        if(!(used[u]&bit)){used[u]|=bit;changed.push_back(u);if(popcount(used[u])==k)possible=false;}
      }
      if(possible&&solve(left-1,max(seen,t+1)))return true;
      color[v]=-1;for(int u:adj[v])if(color[u]<0)degree[u]++;
      for(int u:changed)used[u]^=bit;
      if(nodes>limit)break;
    }
    return false;
 }
};
Box extend(Box b){
 array<int,62> order;iota(order.begin(),order.end(),0);shuffle(order.begin(),order.end(),gen);
 for(int n:order)if(n<31){if(!(rows[n]&b.b))b.a|=1u<<n;}
 else{int j=n-31;bool ok=true;for(M a=b.a;a;a&=a-1)if(rows[countr_zero(a)]>>j&1){ok=false;break;}if(ok)b.b|=1u<<j;}
 return b;
}
int main(){
 ifstream m(".pnp/rect10005-matrix.dat");for(auto& r:rows)m>>r;
 vector<Box> state;Box b;ifstream f(".pnp/known21-10005.dat");while(f>>b.a>>b.b)state.push_back(b);
 for(int run=0;run<100000&&state.size()>15;run++){
    shuffle(state.begin(),state.end(),gen);int len=2+gen()%7,keep=state.size()-len;
    array<M,31> covered{};for(int t=0;t<keep;t++)for(M a=state[t].a;a;a&=a-1)covered[countr_zero(a)]|=state[t].b;
    vector<int> holes;for(int i=0;i<31;i++)for(M a=full&~rows[i]&~covered[i];a;a&=a-1)holes.push_back(31*i+countr_zero(a));
    bool improve=gen()%4;Search s(holes,len-improve);
    if(!s.solve(holes.size(),0))continue;
    vector<Box> change(s.k);for(int i=0;i<(int)holes.size();i++){
      int p=s.cell[i];change[s.color[i]].a|=1u<<(p/31);change[s.color[i]].b|=1u<<(p%31);
    }
    state.resize(keep);
    for(auto x:change)if(x.a&&x.b)state.push_back(extend(x));
    if((int)state.size()<keep+len){
      array<M,31> check{};for(auto x:state)for(M a=x.a;a;a&=a-1)check[countr_zero(a)]|=x.b;
      for(int i=0;i<31;i++)if(check[i]!=(full^rows[i]))return 2;
      cout<<"cover "<<state.size()<<" attempt "<<run<<endl;
      ofstream out(".pnp/neighbor10005-"+to_string(state.size())+".dat");for(auto x:state)out<<x.a<<" "<<x.b<<"\n";
    }
 }
}
