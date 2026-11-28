// A two-curve finite-field obstruction for the primitive septic equation.
// Each line gives q, the number of non-axis slopes compatible with all
// exponents, then the exceptional prime exponents. Empty means q forces an axis.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>
using I=std::int64_t;
bool prime(int n){
    if(n<2)return false;
    for(int d=2;d<=n/d;++d)if(n%d==0)return false;
    return true;
}
std::set<int> large_factors(int n){
    std::set<int> f;
    for(int d=2;d<=n/d;++d)if(n%d==0){
        if(d>=11)f.insert(d);
        do{n/=d;}while(n%d==0);
    }
    if(n>=11)f.insert(n);
    return f;
}
struct Powers {
    int r,i,r3,i3,r5,i5,r7,i7;
};
struct Field {
    int q,nonresidue;
    std::vector<int> chi;
    std::vector<Powers> plane;
    int red(I x)const{int r=x%q;return r<0?r+q:r;}
    int pow(int x,int n)const{
        int a=red(x),v=1;
        for(;n;n/=2,a=red(I(a)*a))if(n%2)v=red(I(v)*a);
        return v;
    }
    explicit Field(int ell):q(ell),chi(q,-1){
        chi[0]=0;
        for(int i=1;i<q;++i)chi[i*i%q]=1;
        nonresidue=2;while(chi[nonresidue]!=-1)++nonresidue;
    }
    int elliptic(int t)const{
        int t2=pow(t,2),t3=pow(t,3),t4=pow(t,4);
        int a2=red(-I(t-1)*(t-1));
        int a4=red(-2*t4+t3-5*t2+t-2);
        int a6=red(pow(t,6)-6*pow(t,5)+8*t4-13*t3+8*t2-6*t+1);
        int sum=0;
        for(int x=0;x<q;++x)sum+=chi[red(((I(x)+a2)*x+a4)*x+a6)];
        return -sum;
    }
    int trace_degree_one(int t)const{
        int t2=pow(t,2),t3=pow(t,3),constant=red(1-pow(t,7));
        int sum=0;
        for(I x=0;x<q;++x){
            int xx=x*x%q;
            int value=red(((I(xx+7*t)*xx+14*t2)*xx+7*t3)*x+constant);
            sum+=chi[value];
        }
        return -sum;
    }
    void make_plane(){
        plane.reserve(q*(q-1)/2);
        for(int i=1;i<=(q-1)/2;++i)for(int r=0;r<q;++r){
            int rr=red(r*r+I(nonresidue)*i*i),ii=red(2*r*i);
            auto step=[&](int ar,int ai){
                return std::pair<int,int>{red(I(ar)*rr+I(nonresidue)*ai*ii),red(I(ar)*ii+I(ai)*rr)};
            };
            auto [r3,i3]=step(r,i);
            auto [r5,i5]=step(r3,i3);
            auto [r7,i7]=step(r5,i5);
            plane.push_back({r,i,r3,i3,r5,i5,r7,i7});
        }
    }
    int trace_degree_two(int t){
        if(plane.empty())make_plane();
        int b5=red(7*t),b3=red(14*pow(t,2)),b1=red(7*pow(t,3)),b0=red(1-pow(t,7));
        int sum=0;
        for(int x=0;x<q;++x)
            sum+=red(pow(x,7)+b5*pow(x,5)+b3*pow(x,3)+b1*x+b0)!=0;
        for(auto z:plane){
            int r=red(z.r7+b5*z.r5+b3*z.r3+b1*z.r+b0);
            int i=red(z.i7+b5*z.i5+b3*z.i3+b1*z.i);
            sum+=2*chi[red(I(r)*r-I(nonresidue)*i*i)];
        }
        return -sum;
    }
};
int main(int argc,char **argv){
    int bound=argc>1?std::atoi(argv[1]):997;
    if(bound<13 || bound>2000)return 2;
    for(int q=13;q<=bound;q+=7){
        if(!prime(q))continue;
        Field f(q);
        int base=f.elliptic(0),unbounded=0;
        std::set<int> exceptions;
        for(int t=1;t<q;++t){
            int e=f.elliptic(t)-base;
            int g;
            if(t==q-1)g=std::gcd(e,q+1);
            else {
                int first=f.trace_degree_one(t);
                g=std::gcd(e,first);
                if(!g || !large_factors(g).empty()){
                    int second=f.trace_degree_two(t);
                    int moment=second+6*q;
                    if(moment<0 || moment>12*q)return 3;
                    if(!moment && !g){++unbounded;continue;}
                    auto candidates=large_factors(std::gcd(g,moment));
                    for(int p:candidates)
                        if(moment%(p*p)==0)exceptions.insert(p);
                    continue;
                }
            }
            if(!g)++unbounded;
            else for(int p:large_factors(g))exceptions.insert(p);
        }
        std::cout<<q<<" "<<unbounded;
        for(int p:exceptions)std::cout<<" "<<p;
        std::cout<<std::endl;
    }
}
