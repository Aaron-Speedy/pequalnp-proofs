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
    erase_if(rects,[&](auto& x){return x.weight<n-(slots-1)*maxarea;});
    cout<<name<<" cells "<<n<<" candidates "<<rects.size()<<" area "<<maxarea<<endl;
    mt19937 gen(9750);
    vector<int> current(slots),best(slots);
    int record=0;
    for(int round=0;round<20000;round++){
        for(int j=0;j<slots;j++)current[j]=(round%5&&j<slots-2)?best[j]:gen()%rects.size();
        shuffle(current.begin(),current.end(),gen);
        for(int iter=0;iter<75;iter++){
            int pos=iter%slots;
            Set other{};
            for(int j=0;j<slots;j++)if(j!=pos)for(int k=0;k<width;k++)other.bits[k]|=rects[current[j]].set.bits[k];
            int mx=0,ties=0,idx=0;
            for(int h=0;h<(int)rects.size();h++){
                int score=0;for(int k=0;k<width;k++)score+=popcount(other.bits[k]|rects[h].set.bits[k]);
                if(score>mx){mx=score;idx=h;ties=1;}else if(score==mx&&gen()%++ties==0)idx=h;
            }
            current[pos]=idx;
            if(mx>record){
                record=mx;best=current;cout<<"covered "<<record<<" round "<<round<<" steps "<<iter<<endl;
                ofstream f(".pnp/rect10005-best-"+name+".dat");
                for(int i:best){Mask r=rects[i].row,c=rects[i].col;for(int j=0;j<order;j++){f<<r<<" "<<c<<"\n";r=perm(r,pr);c=perm(c,pc);}}
                if(mx==n)return 0;
            }
            if((iter+1)%(3*slots)==0)current[gen()%slots]=gen()%rects.size();
        }
    }
}
