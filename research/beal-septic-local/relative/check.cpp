// Septic local test using cyclic coefficients in (Z/p²)[z]/(z^7-1).
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using integer = std::int64_t;
using Polynomial = std::array<integer,7>;

bool prime(int p) {
    for (int d=2; d<=p/d; ++d) if (p%d==0) return false;
    return p>=2;
}

integer mod(integer x, integer modulus) {
    x%=modulus;
    return x<0 ? x+modulus : x;
}

integer power(integer x, integer exponent, integer modulus) {
    integer y=1;
    for (;exponent;exponent/=2) {
        if (exponent%2) y=y*x%modulus;
        x=x*x%modulus;
    }
    return y;
}

Polynomial multiply(const Polynomial& left, const Polynomial& right, integer modulus) {
    // For p<=20000, each coefficient before reduction is below 7*(20000^2)^2.
    std::array<integer,13> product{};
    for (int i=0;i<7;++i)
        for (int j=0;j<7;++j)
            product[i+j]+=left[i]*right[j];
    Polynomial output{};
    for(int j=0;j<7;++j)
        output[j]=(product[j]+(j<6 ? product[j+7] : 0))%modulus;
    return output;
}

Polynomial linear_power(int x, int p) {
    integer modulus=integer(p)*p;
    Polynomial v{1},base{x,1};
    for (int e=p;e;e/=2) {
        if(e%2) v=multiply(v,base,modulus);
        if(e>1) base=multiply(base,base,modulus);
    }
    return v;
}

integer elliptic_trace(int x,int p,const std::vector<int>& symbol) {
    integer h=x,s=(x+1)%p,hh=h*h%p;
    integer c2=mod(4*h-s*s,p);
    integer c4=mod(-2*power(s,4,p)+9*h*power(s,2,p)-11*hh,p);
    integer c6=mod(power(s,6,p)-12*h*power(s,4,p)+41*hh*power(s,2,p)-43*hh*h,p);
    int trace=0;
    for (int z=0;z<p;++z) trace-=symbol[(((z+c2)*z+c4)*z+c6)%p];
    return trace;
}

int main(int argc, char** argv) {
    int limit=argc>1 ? std::atoi(argv[1]) : 1000;
    if(limit<11 || limit>20000) return 2;
    int lower=argc>2 ? std::atoi(argv[2]) : 11;
    if (lower<11 || lower%2==0) return 2;
    for(int p=lower;p<=limit;p+=2) {
        if(!prime(p)) continue;
        integer modulus=integer(p)*p;
        std::vector<int> symbol(p,-1);
        symbol[0]=0;
        for(int x=1;x<p;++x) symbol[x*x%p]=1;
        auto reference=elliptic_trace(0,p,symbol);
        int classes=0,relative=0,rational=0,elliptic=0;
        for(int x=1;x<p;++x) {
            if ((power(x,7,p)+1)%p==0) continue;
            ++classes;
            Polynomial P=linear_power(x,p);
            int h=0;
            bool compatible=true;
            for(int j=1;j<=3;++j) {
                integer slope=mod(P[j]-P[7-j],p);
                integer diff=mod(x*(P[j]-P[7-j])+P[(p+j)%7]-P[(p-j)%7],modulus);
                if (diff%p!=0) return 3;
                if (slope==1) h=mod(-diff/p,p);
                else if (slope==p-1) h=diff/p;
                else if(slope!=0) return 4;
                else if(diff!=0) {compatible=false;break;}
            }
            if(!compatible) continue;
            ++relative;
            integer t=x+integer(p)*h;
            integer num=(power(t,7,modulus)+1)%modulus;
            integer den=power(t+1,7,modulus);
            if(power(num,p-1,modulus)!=power(den,p-1,modulus)) continue;
            ++rational;
            if((elliptic_trace(x,p,symbol)-reference)%p!=0) continue;
            ++elliptic;
            std::cerr<<"surviving non-axis class "<<p<<" "<<x<<" "<<h<<"\n";
        }
        std::cout<<p<<' '<<classes<<' '<<relative<<' '<<rational<<' '<<elliptic<<std::endl;
    }
}
