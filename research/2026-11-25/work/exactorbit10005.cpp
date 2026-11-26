#include <algorithm>
#include <set>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>
using namespace std;
using Mask=uint32_t;
struct Set {array<uint64_t,5> bits{};};
struct Choice {Set set; Mask row,col; int weight;};
Mask perm(Mask v,const array<int,31>& p){
    Mask ans=0;while(v){ans|=1u<<p[countr_zero(v)];v&=v-1;}return ans;
}
int main(int argc,char** argv){
    string name=argv[1];int order=name=="ord3"?3:5;
    int slots=15/order;
    ifstream perms(".pnp/plane10005-"+name+".dat"),table(".pnp/rect10005.dat");
    array<int,31> pr,pc;for(auto& x:pr)perms>>x;for(auto& x:pc)perms>>x;
    int id[31][31];fill(&id[0][0],&id[0][0]+961,-1);
    int n=0;
    vector<Choice> rects; Mask a,b;
    while(table>>a>>b){
        Mask a1=a,b1=b;bool canonical=true;
        for(int k=1;k<order;k++){a1=perm(a1,pr);b1=perm(b1,pc);if(make_pair(a1,b1)<make_pair(a,b)){canonical=false;break;}}
        if(!canonical)continue;
        Choice x{{},a,b,0};
        for(Mask i=a;i;i&=i-1)for(Mask j=b;j;j&=j-1){
            int r=countr_zero(i),c=countr_zero(j);
            if(id[r][c]<0){
                for(int k=0;k<order;k++){id[r][c]=n;r=pr[r];c=pc[c];}
                ++n;
            }
            int p=id[r][c];x.set.bits[p>>6]|=1ull<<(p%64);
        }
        for(auto t:x.set.bits)x.weight+=popcount(t);
        rects.push_back(x);
    }
    int width=(n+63)/64;
    int maxarea=0;for(const auto& x:rects)maxarea=max(maxarea,x.weight);
    erase_if(rects,[&](auto& x){return x.weight<n-(slots-1)*maxarea;});
    cout<<name<<" cells "<<n<<" candidates "<<rects.size()<<" area "<<maxarea<<endl;

    ifstream anchors(".pnp/ord5anchors.dat");
    set<pair<Mask,Mask>> reps;
    while(anchors>>a>>b)reps.emplace(a,b);
    if(reps.empty() || n!=155)return 2;
    int tested=0,feasible=0;
    for(auto& first:rects){
        if(!reps.contains({first.row,first.col}))continue;
        ++tested;
        int residual=n-first.weight, mx=0;
        vector<int> gain;
        for(auto& x:rects){
            int g=0;for(int k=0;k<3;k++)g+=popcount(x.set.bits[k]&~first.set.bits[k]);
            gain.push_back(g);mx=max(mx,g);
        }
        if(2*mx<residual)continue;
        vector<int> ids;
        for(int t=0;t<(int)rects.size();t++)if(gain[t]+mx>=residual)ids.push_back(t);
        ++feasible;
        const int blocks=(ids.size()+63)/64;
        vector<vector<uint64_t>> byCell(n,vector<uint64_t>(blocks));
        vector<int> freq(n);
        for(int h=0;h<(int)ids.size();h++){
            auto& x=rects[ids[h]];
            for(int i=0;i<n;i++)if((x.set.bits[i/64]>>(i%64))&1){
                byCell[i][h/64]|=1ull<<(h%64);++freq[i];
            }
        }
        vector<int> cells;
        for(int i=0;i<n;i++)if(!(first.set.bits[i/64]>>(i%64)&1))cells.push_back(i);
        sort(cells.begin(),cells.end(),[&](int i,int j){return freq[i]<freq[j];});
        for(int h:ids){
            auto& second=rects[h];
            if(!(second.set.bits[cells[0]/64]>>(cells[0]%64)&1))continue;
            vector<int> missing;
            for(int i:cells)if(!(second.set.bits[i/64]>>(i%64)&1))missing.push_back(i);
            for(int q=0;q<blocks;q++){
                uint64_t cand=~0ull;
                for(int i:missing)if(!(cand &= byCell[i][q]))break;
                if(cand){
                    auto& third=rects[ids[q*64+countr_zero(cand)]];
                    for(auto x:{first,second,third}){
                        for(int j=0;j<5;j++){cout<<x.row<<" "<<x.col<<endl;x.row=perm(x.row,pr);x.col=perm(x.col,pc);}
                    }
                    return 0;
                }
            }
        }
    }
    cout<<"exhausted "<<tested<<" eligible representatives ("<<feasible<<" passed two-rectangle area test) out of "<<reps.size()<<endl;
}
