#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std; using M=uint32_t; constexpr M full=(1u<<31)-1;
struct Box{M a=0,b=0;bool operator==(const Box&)const=default;};
array<M,31> nr{},nc{};
M closeSide(M s,const array<M,31>& d){M a=full;while(s){a&=d[countr_zero(s)];s&=s-1;}return a;}
Box byRows(M r){M c=closeSide(r,nr);return {closeSide(c,nc),c};}
Box byCols(M c){M r=closeSide(c,nc);return {r,closeSide(r,nr)};}
int main(int argc,char**argv){
 int K=atoi(argv[1]);mt19937 rng(argc>2?atoi(argv[2]):10005);
 ifstream mat(".pnp/rect10005-matrix.dat");
 for(int i=0;i<31;i++){M r;mat>>r;nr[i]=full^r;for(int j=0;j<31;j++)if(nr[i]>>j&1)nc[j]|=1u<<i;}
 array<vector<M>,31> cs;
 vector<Box> catalog;ifstream in(".pnp/rect10005.dat");Box z;
 while(in>>z.a>>z.b)if(popcount(z.a)*popcount(z.b)>=45)catalog.push_back(z);
 vector<Box> best(K),state(K);int record=776;
 for(int run=0;run<500;run++){
   for(int i=0;i<K;i++)state[i]=catalog[rng()%catalog.size()];
   if(run&&rng()%4){state=best;for(int j=0;j<3;j++)state[rng()%K]=catalog[rng()%catalog.size()];}
   array<array<int,31>,31> w;for(auto& x:w)x.fill(1);
   for(int it=0;it<12000;it++){
      array<M,31> covered{},twice{};for(auto x:state)for(M a=x.a;a;a&=a-1){int i=countr_zero(a);twice[i]|=covered[i]&x.b;covered[i]|=x.b;}
      vector<pair<int,int>> holes;
      for(int i=0;i<31;i++)for(M b=nr[i]&~covered[i];b;b&=b-1)holes.emplace_back(i,countr_zero(b));
      if(int(holes.size())<record){
        record=holes.size();best=state;cout<<"holes "<<record<<" run "<<run<<" step "<<it<<endl;
        ofstream f(".pnp/rect10005-localbest-"+to_string(K)+"-"+argv[2]+".dat");for(auto x:best)f<<x.a<<" "<<x.b<<"\n";
        if(!record)return 0;
      }
      auto [r,c]=holes[rng()%holes.size()];int mx=-10000000,slot=0;Box take{};int ties=0;
      for(int i=0;i<K;i++){
         Box old=state[i];array<M,31> missing;int loss=0;
         for(int j=0;j<31;j++){M unique=((old.a>>j)&1)?old.b&~twice[j]:0; missing[j]=(nr[j]&~covered[j])|unique;
            for(M u=unique;u;u&=u-1)loss+=w[j][countr_zero(u)];}
         auto offer=[&](Box b){
            if(b==old||!b.a||!b.b)return;
            int score=-loss;
            for(M a=b.a;a;a&=a-1){int j=countr_zero(a);for(M h=b.b&missing[j];h;h&=h-1)score+=w[j][countr_zero(h)];}
            if(score>mx){mx=score;ties=1;slot=i;take=b;}else if(score==mx && rng()%++ties==0){slot=i;take=b;}
         };
         M a=(old.a&nc[c])|(1u<<r),b=(old.b&nr[r])|(1u<<c);
         offer(byRows(a));offer(byCols(b));
         for(int j=0;j<3;j++){
             M mask=rng();offer(byRows((a&mask)|(1u<<r)));offer(byCols((b&mask)|(1u<<c)));
             Box q=catalog[rng()%catalog.size()];offer(byRows((q.a&nc[c])|(1u<<r)));
         }
      }
      state[slot]=take;
      if(mx<=0&&rng()%4==0)for(auto [u,v]:holes)++w[u][v];
      if(it%400==399)for(auto& row:w)for(auto& a:row)a=(a+2)/2;
   }
 }
}
