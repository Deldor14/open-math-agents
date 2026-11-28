// Independent verifier using roots of irreducible quadratic polynomials.
// It uses the chart (a,b)=(x,1-x) and the invariants of the elliptic model
// expressed in terms of s=a+b, h=ab.
#include <algorithm>
#include <array>
#include <cmath>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>

using integer = long long;

bool is_prime(int n) {
    if (n < 2) return false;
    for (int j=2; j*j<=n; ++j) if (n%j==0) return false;
    return true;
}

class Counter {
    int q;
    std::vector<int> character;
    std::vector<std::array<int, 10>> quadratics;

    int mod(integer x) const { return int((x%q+q)%q); }

    void prepare_quadratics() {
        for (int trace=0; trace<q; ++trace) {
            for (int norm=0; norm<q; ++norm) {
                if (character[mod(trace*trace-4*norm)]!=-1) continue;
                std::array<int,10> poly{trace,norm};
                int linear=0, constant=1;
                for (int j=1; j<=7; ++j) {
                    int new_linear=mod(linear*trace+constant);
                    constant=mod(-norm*linear);
                    linear=new_linear;
                    if (j%2) {
                        poly[j+1]=linear;
                        poly[j+2]=constant;
                    }
                }
                quadratics.push_back(poly);
            }
        }
    }

public:
    explicit Counter(int prime):q(prime),character(q,-1) {
        character[0]=0;
        for (int x=1; x<q; ++x) character[mod(x*x)]=1;
    }

    int power(int x, int n) const {
        int value=1;
        for(int i=0; i<n; ++i) value=mod(value*x);
        return value;
    }

    int elliptic_trace(int a,int b) const {
        // c4=-2s^4+9hs^2-11h^2, c6=s^6-12hs^4+41h^2s^2-43h^3.
        int s=mod(a+b), h=mod(a*b), h2=mod(h*h);
        int e2=mod(4*h-power(s,2));
        int e4=mod(-2*power(s,4)+9*h*power(s,2)-11*h2);
        int e6=mod(power(s,6)-12*h*power(s,4)+41*h2*power(s,2)-43*h2*h);
        int trace=0;
        for (int x=0; x<q; ++x)
            trace-=character[mod(power(x,3)+e2*power(x,2)+e4*x+e6)];
        return trace;
    }

    std::array<int,5> coefficients(int a,int b) const {
        int h=mod(a*b);
        return {mod(7*power(h,3)),mod(14*power(h,2)),mod(7*h),1,
                mod(power(b,7)-power(a,7))};
    }

    int polynomial(int x, const std::array<int,5>& c) const {
        int value=c[4];
        for (int k=0; k<4; ++k) value+=c[k]*power(x,2*k+1);
        return mod(value);
    }

    int trace_one(const std::array<int,5>& c) const {
        int total=0;
        for (int x=0; x<q; ++x) total-=character[polynomial(x,c)];
        return total;
    }

    int trace_two(const std::array<int,5>& c) {
        if (quadratics.empty()) prepare_quadratics();
        int total=0;
        for (int x=0; x<q; ++x) total-=polynomial(x,c)!=0;
        for (const auto& poly:quadratics) {
            int linear=0, constant=c[4];
            for (int k=0; k<4; ++k) {
                linear+=c[k]*poly[2+2*k];
                constant+=c[k]*poly[3+2*k];
            }
            integer u=mod(linear), v=mod(constant);
            total-=2*character[mod(u*u*poly[1]+u*v*poly[0]+v*v)];
        }
        return total;
    }
};

int main() {
    for (int q=2; q<=997; ++q) {
        if (!is_prime(q) || q%7!=6) continue;
        Counter field(q);
        auto reference=field.coefficients(0,1);
        if (field.trace_one(reference)!=0 || field.trace_two(reference)!=-6*q) return 1;
        int base=field.elliptic_trace(1,0);
        int unrestricted=0;
        std::set<int> exceptions;
        for (int x=1; x<q; ++x) {
            // x=1 encodes the missing slope a+b=0. Otherwise x=a/(a+b).
            int a=x, b=(x==1 ? -1 : 1-x);
            int delta=field.elliptic_trace(a,b)-base;
            if (x==1) {
                for (int p=11;p<=q+1;++p)
                    if (is_prime(p) && (q+1)%p==0 && delta%p==0) exceptions.insert(p);
                continue;
            }
            auto c=field.coefficients(a,b);
            int trace=field.trace_one(c);
            std::vector<int> candidates;
            int bound=std::max(10, std::max(std::abs(trace),std::abs(delta)));
            // If both differences vanish, a nonzero moment bounds p by sqrt(12q).
            if (delta==0 && trace==0) bound=int(std::sqrt(12*q))+1;
            for (int p=11; p<=bound; ++p) {
                if (is_prime(p) && delta%p==0 && trace%p==0) candidates.push_back(p);
            }
            if (candidates.empty() && (delta!=0 || trace!=0)) continue;
            int moment=field.trace_two(c)+6*q;
            if (moment<0 || moment>12*q) return 2;
            if (moment==0 && delta==0 && trace==0) ++unrestricted;
            for (int p:candidates) if (moment%(p*p)==0) exceptions.insert(p);
        }
        std::cout<<q<<' '<<unrestricted;
        for(int p:exceptions) std::cout<<' '<<p;
        std::cout<<std::endl;
    }
}
