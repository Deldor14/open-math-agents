// Local necessary tests for the pure cyclotomic equation a+b*zeta = beta^p.
#include <array>
#include <cstdint>
#include <iostream>
#include <cstdlib>
using Int = std::int64_t;
using Poly = std::array<Int,7>;

Poly multiply(const Poly& a,const Poly& b,Int modulus) {
    Poly c{};
    for(int i=0;i<7;++i)
        for(int j=0;j<7;++j)
            c[(i+j)%7]+=a[i]*b[j];
    // Each sum is at most 7*(20000^2-1)^2 < 2^63.
    for(auto& entry:c) entry%=modulus;
    return c;
}

Poly power(Poly base,int n,Int modulus) {
    Poly out{1};
    while(n) {
        if(n%2) out=multiply(out,base,modulus);
        n/=2;
        if(n) base=multiply(base,base,modulus);
    }
    return out;
}

bool prime(int p) {
    for(int j=2;j<=p/j;++j) if(p%j==0) return false;
    return true;
}

int main(int argc,char** argv) {
    int bound=argc>1?std::atoi(argv[1]):20000;
    if(bound<11 || bound>20000) return 2;
    for(int p=11;p<=bound;p+=2) {
        if(!prime(p)) continue;
        Int mod=Int(p)*p;
        int ordinary=0;
        for(int x=1;x<p-1;++x) {
            auto v=power(Poly{Int(x),1},p,mod);
            bool ok=true;
            for(int j=1;j<7;++j)
                if(j!=p%7 && v[j]!=0) ok=false;
            if(ok) { ++ordinary; std::cerr<<"candidate "<<p<<' '<<x<<'\n'; }
        }
        // D divisible by p gives t=-1 mod p^2. Test E=(z-1)^6/7.
        Poly v{mod-1,1}, w{mod-1};
        w[p%7]=1;
        auto left=power(v,6*p,mod);
        auto right=power(w,6,mod);
        Int seven=power(Poly{7},p,mod)[0];
        Poly difference{};
        for(int i=0;i<7;++i) difference[i]=(7*left[i]-seven*right[i])%mod;
        bool special=true;
        for(int i=1;i<7;++i)
            if((difference[i]-difference[0])%mod!=0) special=false;
        std::cout<<p<<' '<<p-2<<' '<<ordinary<<' '<<special<<std::endl;
    }
}
