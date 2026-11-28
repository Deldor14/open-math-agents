// Independent exact checker. Input contains only lower cells and their first layer.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

using i64 = std::int64_t;
struct Row {
    int first;
    std::vector<std::pair<int,int>> arcs;
};
void require(bool value, const char *message) {
    if (!value) throw std::runtime_error(message);
}
int wrap(int x, int n) { int r=x%n; return r<0 ? r+n : r; }

int best_half(const std::vector<int>& v) {
    int n=v.size(), total=0;
    for (int i=0;i<n/2;++i) total+=v[i];
    int best=total;
    for (int i=0;i<n-1;++i) {
        total+=v[(i+n/2)%n]-v[i];
        best=std::max(best,total);
    }
    return best;
}
bool overlap_mod(int a,int b,int l,int r,int n) {
    for(int j=-2;j<=2;++j)
        if(std::max(a,l+j*n)<std::min(b,r+j*n)) return true;
    return false;
}
void verify_lower(const std::vector<Row>& rows, int k) {
    const int n=rows.size();
    for(int i=0;i<n;++i) {
        const Row& row=rows[i];
        if(row.first==k) continue;
        if(i<n/2) {
            require(row.arcs.size()<=1,"lower chart has several arcs");
            for(auto [a,b]:row.arcs) require(2*(b-a)<=n,"long lower arc");
        } else {
            bool pos=false, neg=false;
            int lp=0, ln=0, top=-n;
            for(auto [a,b]:row.arcs) {
                require(a>=0 || b<=0,"arc crosses sign boundary");
                bool is_pos=(a>=0);
                require(is_pos ? !pos : !neg,"duplicate signed arc");
                int shift=is_pos ? -n/2 : n/2;
                int lo=2*a+shift, hi=2*b+shift;
                require(lo>=-n/2 && hi<=n/2,"folded arc outside chart");
                if(is_pos) { pos=true; lp=lo; } else { neg=true; ln=lo; }
                top=std::max(top,hi);
            }
            if(pos && neg) require(2*top<=lp+ln+n,"possible upward angular half-jump");
        }
    }
    // A primary upward carry requires i+j+n-2p in {-1,0,1}.
    for(int p=0;p<n;++p) {
        if(rows[p].first==k || rows[p].arcs.empty()) continue;
        for(int total=2*p-n-1;total<=2*p-n+1;++total) {
            for(int i=std::max(0,total-n+1);i<=total/2 && i<=total;++i) {
                int j=total-i;
                if(rows[i].first==k || rows[j].first==k) continue;
                for(auto [a,b]:rows[i].arcs) for(auto [c,d]:rows[j].arcs)
                    for(auto [l,r]:rows[p].arcs)
                        require(!overlap_mod(a+c,b+d,2*l,2*r,n),"lower primary carry");
            }
        }
    }
}
int main(int argc,char** argv) {
    require(argc==2,"pass lower.tsv");
    std::ifstream input(argv[1]);
    int n,k;
    require(bool(input>>n>>k) && n==2048 && k==96,"unexpected dimensions");
    std::vector<Row> rows(n);
    i64 lower=0, upper=0;
    for(int i=0;i<n;++i) {
        int index,count;
        Row& row=rows[i];
        require(bool(input>>index>>row.first>>count) && index==i &&
                row.first>=0 && row.first<=k && count>=0 && count<=2,"bad row");
        for(int j=0;j<count;++j) {
            int a,b;require(bool(input>>a>>b) && -n/2<=a && a<b && b<=n/2,"bad interval");
            for(auto [l,r]:row.arcs) require(b<=l || r<=a,"intersecting arcs");
            row.arcs.emplace_back(a,b);
            lower+=i64(k-row.first)*(b-a);
        }
    }
    std::string rest;require(!(input>>rest),"unexpected data");
    verify_lower(rows,k);
    std::vector<std::vector<int>> widths(k,std::vector<int>(n));
    for(int p=0;p<n;++p) {
        // Difference arrays by first prohibited upper band, with a separate sweep per s-column.
        std::vector<std::vector<int>> diff(k,std::vector<int>(n+1));
        for(int i=0;i<n;++i) for(int carry=0;carry<=1;++carry) {
            int j=wrap(p-i-carry,n);
            int h=rows[i].first+rows[j].first;
            if(h>=k) continue;
            for(auto [a,b]:rows[i].arcs) for(auto [c,d]:rows[j].arcs) {
                int begin=wrap(a+c,n),len=b+d-a-c,end=begin+len;
                if(len>=n) { ++diff[h][0]; --diff[h][n]; }
                else if(end<=n) { ++diff[h][begin]; --diff[h][end]; }
                else { ++diff[h][begin]; --diff[h][n]; ++diff[h][0]; --diff[h][end-n]; }
            }
        }
        std::vector<int> available(n,1);
        for(int h=0;h<k;++h) {
            int active=0;
            for(int t=0;t<n;++t) {
                active+=diff[h][t];
                require(active>=0,"invalid interval count");
                if(active>0) available[t]=0;
            }
            require(active+diff[h][n]==0,"unbalanced interval sweep");
            widths[h][p]=best_half(available);
        }
    }
    for(const auto& w:widths) upper+=best_half(w);
    require(lower==98713058 && upper==75594412,"cell totals differ from the claim");
    require(2*lower+upper==16LL*17063783 && 4LL*k*n*n==16LL*100663296,"wrong normalized volume");
    std::cout<<"Checked all lower carries and local charts. Lower "<<lower
             <<", upper "<<upper<<", volume 17063783/100663296.\n";
}
