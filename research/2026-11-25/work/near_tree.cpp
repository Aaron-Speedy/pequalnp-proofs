// Exhaust connected circuits close to the k-1 binary-gate bound.
// Number inputs by first use and recognize all input permutations at the end.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_set>
using Word = std::uint64_t;
using Wires = std::array<Word, 16>;
std::array<Word, 6> inputs;
std::unordered_set<Word> targets;
std::uint64_t terminals = 0;
bool visit(Wires live, int count, int fresh, int binary, int neg, int copies) {
    if (binary + neg == 0) {
        if (fresh != 6 || count != 1 || copies != 0) return false;
        ++terminals;
        return targets.contains(live[0]);
    }
    // Unseen inputs can appear only consecutively, in ascending order.
    Wires avail = live;
    int end = count;
    for (int j = fresh; j < std::min(6, fresh + 2); ++j) avail[end++] = inputs[j];
    for (int i = 0; i < end && i <= count; ++i) {
        for (int j = i; j < end; ++j) {
            bool unary = i == j;
            if (unary ? !neg : !binary) continue;
            if (j == count + 1 && i != count) continue;
            int newinputs = (i >= count) + (!unary && j >= count);
            for (unsigned keep = 0; keep < (unary ? 2u : 4u); ++keep) {
                int retained = std::popcount(keep);
                if (retained > copies) continue;
                Wires next{};
                int n = 0;
                for (int z = 0; z < count; ++z)
                    if (z != i && z != j) next[n++] = live[z];
                if (keep & 1) next[n++] = avail[i];
                if (keep & 2) next[n++] = avail[j];
                for (int op = 0; op < (unary ? 1 : 2); ++op) {
                    Word out = unary ? ~avail[i] : (op ? avail[i] | avail[j] : avail[i] & avail[j]);
                    next[n] = out;
                    if (visit(next, n+1, fresh+newinputs, binary-!unary, neg-unary, copies-retained)) return true;
                }
            }
        }
    }
    return false;
}
int main(int argc, char** argv) {
    if (argc < 2 || argc > 3) return 2;
    int maxSize = argc == 3 ? std::stoi(argv[2]) : 7;
    if (maxSize < 6 || maxSize > 8) return 2;
    Word target = std::stoull(argv[1]);
    for (int k=0; k<6; ++k)
        for (int r=0; r<64; ++r) if ((r>>k)&1) inputs[k] |= Word(1)<<r;
    std::array<int,6> p{0,1,2,3,4,5};
    do {
        Word t = 0;
        for(int r=0; r<64; ++r) {
            int key = 0;
            for(int k=0; k<6; ++k) key |= ((r>>k)&1)<<p[k];
            t |= ((target>>key)&1)<<r;
        }
        targets.insert(t);
    } while(std::next_permutation(p.begin(),p.end()));
    // With six essential inputs, every connected normalized circuit uses
    // at least five binary gates. The number of extra reads equals b - 5.
    for(int size=6; size<=maxSize; ++size) for(int b=5;b<size;++b) {
        terminals = 0;
        bool found=visit({},0,0,b,size-b,b-5);
        std::cout<<b<<" binary, "<<size-b<<" NOT: "<<(found?"match":"absent")<<", "<<terminals<<" terminal circuits\n";
    }
}
