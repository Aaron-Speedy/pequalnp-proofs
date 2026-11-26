#include <algorithm>
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

    ifstream fixed(".pnp/fixed10005-"+name+".dat");
    Set occupied{};
    while(fixed>>a>>b){
        for(Mask i=a;i;i&=i-1)for(Mask j=b;j;j&=j-1){
            int p=id[countr_zero(i)][countr_zero(j)];
            if(p<0)return 2;
            occupied.bits[p/64]|=1ull<<(p%64);
        }
    }
    int rem=n;
    for(auto v:occupied.bits)rem-=popcount(v);
    int most=0;
    for(auto& x:rects){
        int gain=0;
        for(int k=0;k<width;k++)gain+=popcount(x.set.bits[k]&~occupied.bits[k]);
        most=max(most,gain);
    }
    cout<<name<<" uncovered by all fixed boxes "<<rem<<" max gain from moving orbit "<<most<<endl;
    if(2*most<rem)return 0;
    vector<Choice> high;
    for(auto& x:rects){
        int gain=0;for(int k=0;k<width;k++)gain+=popcount(x.set.bits[k]&~occupied.bits[k]);
        if(gain+most>=rem)high.push_back(x);
    }
    cout<<"eligible candidates "<<high.size()<<endl;
    long long pairs=0;
    for(int i=0;i<(int)high.size();i++)for(int j=i+1;j<(int)high.size();j++){
        bool ok=true;
        for(int k=0;k<width;k++){
            auto all=k+1==width && n%64 ? (1ull<<(n%64))-1 : ~0ull;
            if((occupied.bits[k]|high[i].set.bits[k]|high[j].set.bits[k])!=all){ok=false;break;}
        }
        pairs+=ok;
    }
    cout<<"pairs covering all residual cells "<<pairs<<endl;
}
