#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
constexpr int N=775,MAXK=22;
struct Cell {int r,c;};
struct Box {unsigned r,c;};
int main(){
    mt19937 rng(10005); array<unsigned,31> matrix;
    ifstream f(".pnp/rect10005-matrix.dat"); for(auto& r:matrix)f>>r;
    vector<Cell> cells;
    for(int i=0;i<31;i++)for(int j=0;j<31;j++)if(!(matrix[i]>>j&1))cells.push_back({i,j});
    array<vector<int>,N> adj;
    for(int i=0;i<N;i++)for(int j=0;j<N;j++){
        auto a=cells[i],b=cells[j];
        if((matrix[a.r]>>b.c | matrix[b.r]>>a.c)&1)adj[i].push_back(j);
    }
    vector<Box> boxes; Box z;ifstream start(".pnp/known21-10005.dat");while(start>>z.r>>z.c)boxes.push_back(z);
    vector<int> best(N,-1);
    for(int i=0;i<N;i++){
        vector<int> opts;
        for(int j=0;j<(int)boxes.size();j++)if((boxes[j].r>>cells[i].r & boxes[j].c>>cells[i].c)&1)opts.push_back(j);
        if(opts.empty())return 2;
        best[i]=opts[rng()%opts.size()];
    }
    for(int k=boxes.size()-1;k>=15;k--){
        vector<int> cnt(k+1);
        for(int v:best)if(v>=0)cnt[v]++;
        int drop=min_element(cnt.begin(),cnt.end())-cnt.begin();
        for(auto& v:best)if(v==drop)v=-1;else if(v==k)v=drop;
        int rec=count(best.begin(),best.end(),-1);
        for(int run=0;rec;run++){
            vector<int> col=best;
            if(run)for(int a=0;a<4+run%35;a++)col[rng()%N]=-1;
            array<array<int,MAXK>,N> bad{},tabu{};
            for(int i=0;i<N;i++)if(col[i]>=0)for(int u:adj[i])bad[u][col[i]]++;
            int holes=count(col.begin(),col.end(),-1);
            int stale=0;
            for(int step=1;step<100000&&stale<5000;step++){
                int val=100000,chosen=-1,label=-1,ties=0;
                for(int v=0;v<N;v++)if(col[v]<0)for(int l=0;l<k;l++){
                    int cost=bad[v][l];
                    if(tabu[v][l]>=step && holes+cost-1>=rec)continue;
                    if(cost<val){chosen=v;label=l;val=cost;ties=1;}
                    else if(cost==val&&rng()%++ties==0){chosen=v;label=l;}
                }
                if(chosen<0)break;
                col[chosen]=label;
                for(int u:adj[chosen]){
                    bad[u][label]++;
                    if(col[u]!=label)continue;
                    col[u]=-1;tabu[u][label]=step+5+rng()%12+holes/2;
                    for(int w:adj[u])bad[w][label]--;
                }
                holes+=val-1;stale++;
                if(holes<rec){
                    rec=holes;best=col;stale=0;
                    cout<<k<<" colors, "<<rec<<" unassigned, restart "<<run<<endl;
                    if(!rec)break;
                }
            }
        }
        vector<Box> cover(k);
        for(int i=0;i<N;i++){cover[best[i]].r|=1u<<cells[i].r;cover[best[i]].c|=1u<<cells[i].c;}
        ofstream out(".pnp/partial10005-"+to_string(k)+".dat");
        for(auto b:cover)out<<b.r<<" "<<b.c<<"\n";
    }
}
