// Exact upper integral for a translate-periodic atlas on the D3 parity body.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using std::int64_t;

int width_upper(int k, bool low, int n) {
    // q=n(s-x) lies between k-1 and k+1. On the low x half
    // the width is max(0,min(q,3n-2q)); on the high x half
    // it is max(0,min(q,n-q)). Both tents attain their maximum at a grid point.
    const int peak = low ? n : n/2;
    const int q = std::clamp(peak, k-1, k+1);
    return std::max(0,std::min(q,low ? 3*n-2*q : n-q));
}

int main(int argc,char** argv) {
    const int n=argc>=2 ? std::atoi(argv[1]) : 600;
    if (n<6 || n>3600 || n%6) return 1;
    const bool circle_cap = argc==3 && std::string(argv[2])=="circle";
    constexpr int64_t area_num=304098, area_den=1000000;
    int64_t aggregate=0;
    std::vector<int> width(n),adjacent(2*n);
    for (int i=0;i<2*n;++i) {
        int total=0;
        for (int j=0;j<n;++j) {
            width[j]=std::min(circle_cap ? n/2 : n,width_upper(i-j,j<n/2,n));
            total+=width[j];
        }
        for (int j=0;j<2*n;++j)
            adjacent[j]=std::max(width[j%n],width[(j+1)%n]);
        int best=0;
        for (int h=n/3;h<=n/2;++h) {
            int overlap=0;
            for (int j=0;j<n;++j)
                overlap+=std::min(width[j],adjacent[j+h]);
            best=std::max(best,overlap);
        }
        int64_t a=area_num*n*n;
        aggregate+=std::min({2*a, 2*area_den*total, a+area_den*best});
    }
    // At n <= 3600 the numerator is at most 4*area_num*n^3 < 2^63.
    std::cout << n << " " << aggregate << "/" << 4*area_den*n*n*n << "\n";
}
