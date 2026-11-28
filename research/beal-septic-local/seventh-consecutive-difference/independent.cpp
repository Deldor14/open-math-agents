// Enumerate the numerator v for each exponent class by Chinese remaindering.
// The inverse exponent maps the image of the difference polynomial back to v.
#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <vector>

using Int = long long;
const int W=5040;
const Int bound=1000000000;

int powmod(Int a, int k, int q) {
    if (k==0) return 1;
    Int half=powmod(a,k/2,q);
    Int sq=half*half%q;
    return static_cast<int>(k%2 ? sq*(a%q)%q : sq);
}

int inverse(int a, int modulus) {
    int x=1,y=0, r=a,s=modulus;
    while (s) {
        int quotient=r/s;
        int next_r=r-quotient*s, next_x=x-quotient*y;
        r=s; s=next_r; x=y; y=next_x;
    }
    return (x%modulus+modulus)%modulus;
}

struct Filter {
    int q;
    std::vector<int> image;
    explicit Filter(int m):q(m) {
        // t=A(A+D)/D^2. For D=1 the polynomial equals 1+7*t*(t+1)^2.
        std::vector<bool> seen(q,false);
        for (Int a=0; a<q; ++a) {
            Int t=a*(a+1)%q;
            int value=static_cast<int>((1+7*t*(t+1)*(t+1))%q);
            if (!seen[value]) {seen[value]=true;image.push_back(value);}
        }
    }
};

int main() {
    const std::vector<int> first={29,31,37,41};
    std::vector<Filter> filters;
    for (int q:first) filters.emplace_back(q);
    for (int q=5; q<=W+1; ++q) {
        if (W%(q-1) || q==7 || std::find(first.begin(),first.end(),q)!=first.end()) continue;
        bool prime=true;
        for (int k=2;k*k<=q;++k) if (!(q%k)) prime=false;
        if (prime) filters.emplace_back(q);
    }
    std::vector<std::array<int,3>> result;
    for (int e=1; e<W; ++e) {
        if (std::gcd(e,W)!=1) continue;
        std::vector<std::vector<int>> origins;
        for (const auto& f:filters) {
            std::vector<int> row;
            int inv=inverse(e,f.q-1);
            for (int z:f.image) row.push_back(powmod(z,inv,f.q));
            origins.push_back(std::move(row));
        }
        for (int d=1; d<20; d+=2) {
            if (d%7==0) continue;
            Int sixth=static_cast<Int>(d)*d*d*d*d*d;
            std::vector<Int> candidates={1};
            Int modulus=42;
            std::vector<std::vector<char>> rest;
            std::vector<int> moduli;
            for (std::size_t j=0;j<filters.size();++j) {
                int q=filters[j].q;
                if (d%q==0) continue;
                if (j<first.size()) {
                    std::vector<Int> next;
                    int inv=inverse(static_cast<int>(modulus%q),q);
                    // inv*target is independent of the old residue.
                    std::vector<int> translated;
                    for (int z:origins[j]) translated.push_back(sixth%q*z%q*inv%q);
                    for (Int prior:candidates) {
                        int correction=prior%q*inv%q;
                        for (int z:translated) {
                            int k=z-correction;
                            if (k<0) k+=q;
                            Int v=prior+modulus*k;
                            if (v<=bound/d) next.push_back(v);
                        }
                    }
                    candidates.swap(next);
                    modulus*=q;
                } else {
                    std::vector<char> allowed(q);
                    for (int z:origins[j]) allowed[sixth%q*z%q]=1;
                    moduli.push_back(q);
                    rest.push_back(std::move(allowed));
                }
            }
            for (Int start:candidates) {
                for (Int v=start;v<=bound/d;v+=modulus) {
                    if (v<=sixth) continue;
                    bool ok=true;
                    for (std::size_t j=0;j<moduli.size();++j)
                        if (!rest[j][v%moduli[j]]) {ok=false;break;}
                    if (ok && std::gcd(v,static_cast<Int>(d))==1)
                        result.push_back({d,static_cast<int>(v),e});
                }
            }
        }
    }
    std::sort(result.begin(),result.end());
    for (auto row:result) std::cout<<row[0]<<' '<<row[1]<<' '<<row[2]<<'\n';
}
