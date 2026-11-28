// Direct exhaustive calculation in (Z/m)[z]/(z^5-1), projecting to Phi_5 only at comparison.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Integer = std::int64_t;
using Polynomial = std::array<Integer,5>;
const Polynomial one{1,0,0,0,0}, epsilon{1,1,0,0,1};

Polynomial multiply(const Polynomial& a, const Polynomial& b, Integer m) {
    Polynomial c{};
    for (int i=0; i<5; ++i)
        for (int j=0; j<5; ++j)
            c[(i+j)%5] += a[i]*b[j];
    for (auto& t:c) t %= m;
    return c;
}
Polynomial power(Polynomial a, Integer e, Integer m) {
    Polynomial b=one;
    while (e>0) {
        if (e%2) b=multiply(b,a,m);
        a=multiply(a,a,m);
        e/=2;
    }
    // The kernel of the projection is precisely the multiples of (1,1,1,1,1).
    Integer last=b[4];
    for (auto& t:b) t=(t-last+m)%m;
    return b;
}
void require(bool condition, const std::string& message) {
    if (!condition) throw std::runtime_error(message);
}
bool prime(Integer n) {
    if (n<2) return false;
    for (Integer d=2; d*d<=n; ++d) if (n%d==0) return false;
    return true;
}
void test(Integer p, Integer m, Integer e, bool exponent_prime) {
    std::map<Polynomial,std::vector<Integer>> targets;
    if (exponent_prime) {
        for (int j=0; j<p; ++j) targets[power(epsilon,e*j,m)].push_back(j);
        require(Integer(targets.size())==p && power(epsilon,e*p,m)==one, "unit order");
    } else {
        for (auto j:std::array<Integer,2>{0,p/2}) targets[power(epsilon,e*j,m)].push_back(j);
    }
    using Pair = std::pair<Integer,Integer>;
    std::vector<Pair> matches;
    for (Integer x=0; x<m; ++x) {
        auto value=power({(1-x+m)%m,x,0,0,0},e,m);
        auto it=targets.find(value);
        if (it!=targets.end()) for (auto j:it->second) matches.emplace_back(j,x);
    }
    require(matches==std::vector<Pair>{{0,0},{0,1}}, "unexpected matches at "+std::to_string(m));
}
int main(int argc, char** argv) {
    require(argc==2, "supply the witness table path");
    std::ifstream in(argv[1]);
    require(bool(in), "cannot open witness table");
    std::string line;
    std::vector<Integer> primes;
    int auxiliary_count=0;
    while (std::getline(in,line)) {
        std::istringstream row(line);
        Integer p,q;
        require(bool(row>>p) && p>=29 && p<=239 && prime(p) && p%5!=1, "bad exponent");
        primes.push_back(p);
        Integer n=p;
        while (n%5!=1) n*=p;
        test(p,p*p,n-1,true);
        std::vector<Integer> checked;
        while (row>>q) {
            require(q<100000 && prime(q) && q%p==1 && q%5==4, "bad auxiliary prime");
            require(std::find(checked.begin(),checked.end(),q)==checked.end(), "repeated prime");
            checked.push_back(q);
            test(p,q,(q*q-1)/p,false);
        }
        require(!checked.empty() && row.eof(), "invalid row");
        auxiliary_count+=int(checked.size());
    }
    std::vector<Integer> expected;
    for (int p=29; p<=239; ++p) if (prime(p) && p%5!=1) expected.push_back(p);
    require(primes==expected, "incomplete range");
    std::cout<<"Direct cyclic convolution verified "<<primes.size()<<" exponent-prime tables and "
             <<auxiliary_count<<" auxiliary-prime tables.\n";
}
