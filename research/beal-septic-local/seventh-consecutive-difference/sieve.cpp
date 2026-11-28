// Enumerate every possible (d,v,n mod 5040) with d*v <= one billion.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>

constexpr int period = 5040;
constexpr int words = 18; // phi(5040) = 1152.
using Mask = std::array<std::uint64_t, words>;

int power(int base, int exponent, int modulus) {
    long long result = 1;
    long long factor = base;
    while (exponent) {
        if (exponent & 1) result = result * factor % modulus;
        factor = factor * factor % modulus;
        exponent >>= 1;
    }
    return static_cast<int>(result);
}

bool prime(int n) {
    for (int d=2; d*d<=n; ++d) if (n%d == 0) return false;
    return n > 1;
}

struct Test {
    int q;
    std::vector<bool> image;
    explicit Test(int modulus) : q(modulus), image(q) {
        for (int a=0; a<q; ++a) {
            int value = (power(a+1,7,q)-power(a,7,q)+q)%q;
            image[value] = true;
        }
    }
};

struct Wheel {
    int q;
    std::vector<Mask> permitted;
    Wheel(const Test& test, const std::vector<int>& classes) :
        q(test.q), permitted(q, Mask{}) {
        for (int b=0; b<q; ++b) {
            for (std::size_t i=0; i<classes.size(); ++i) {
                if (test.image[power(b,classes[i],q)])
                    permitted[b][i/64] |= std::uint64_t{1} << (i%64);
            }
        }
    }
};

void scan(int d, const std::vector<int>& classes) {
    const int limit=1000000000;
    long long sixth=1;
    for (int i=0; i<6; ++i) sixth*=d;
    std::vector<Wheel> wheels;
    for (int q=5; q<=period+1; ++q) {
        if (period%(q-1) || !prime(q) || d%q==0) continue;
        Test test(q);
        // Model (v/d^6)^n = (x+1)^7-x^7 over F_q. Precompose each
        // residue lookup with division by d^6 when constructing the wheel.
        wheels.emplace_back(test,classes);
    }
    for (Wheel& w : wheels) {
        auto unscaled=w.permitted;
        int inv=power(static_cast<int>(sixth%w.q),w.q-2,w.q);
        for (int v=0; v<w.q; ++v) w.permitted[v]=unscaled[v*inv%w.q];
    }
    for (int b=1+42*static_cast<int>((sixth+41)/42); b<=limit/d; b+=42) {
        if (std::gcd(b,d)!=1) continue;
        Mask active;
        active.fill(UINT64_MAX);
        bool some=true;
        for (const Wheel& w : wheels) {
            const Mask& allowed=w.permitted[b%w.q];
            std::uint64_t any=0;
            for (int j=0; j<words; ++j) {
                active[j] &= allowed[j];
                any |= active[j];
            }
            if (!any) {some=false; break;}
        }
        if (!some) continue;
        for (int j=0; j<words; ++j) {
            auto bits=active[j];
            while (bits) {
                int i=j*64+__builtin_ctzll(bits);
                bits &= bits-1;
                std::cout << d << ' ' << b << ' ' << classes[i] << '\n';
            }
        }
    }
}

int main() {
    std::vector<int> classes;
    for (int i=1; i<period; ++i)
        if (std::gcd(i,period)==1) classes.push_back(i);
    if (classes.size()!=64*words) return 2;
    for (int d=1; d<20; ++d)
        if (std::gcd(d,14)==1) scan(d,classes);
}
