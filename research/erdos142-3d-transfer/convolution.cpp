// Exact cyclic sumset convolution. Each lower spatial square is born once.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <vector>
using Cell=std::uint32_t;
using Wide=std::uint64_t;
constexpr Cell prime=998244353;
Cell times(Cell a,Cell b) { return Wide(a)*b%prime; }
Cell power(Cell a, Cell n) {
    Cell z=1;
    for(; n; n>>=1,a=times(a,a)) if(n&1) z=times(z,a);
    return z;
}
struct Transform {
    int n;
    std::vector<int> rev;
    std::vector<Cell> roots;
    Transform(int len,bool inverse):n(len),rev(n),roots(n) {
        if (n<2 || (n&(n-1)) || (prime-1)%n) throw std::runtime_error("invalid transform size");
        int bits=0;while((1<<bits)<n) ++bits;
        for(int i=1;i<n;++i) rev[i]=(rev[i/2]/2)+((i&1)<<(bits-1));
        for(int step=1;step<n;step*=2) {
            Cell omega=power(3,(prime-1)/(2*step));
            if(inverse) omega=power(omega,prime-2);
            roots[step]=1;
            for(int j=1;j<step;++j) roots[step+j]=times(roots[step+j-1],omega);
        }
    }
    void apply(Cell* v) const {
        for(int i=0;i<n;++i) if(i<rev[i]) std::swap(v[i],v[rev[i]]);
        for(int step=1;step<n;step*=2) for(int block=0;block<n;block+=2*step)
            for(int j=0;j<step;++j) {
                Cell a=v[block+j], b=times(v[block+j+step],roots[step+j]);
                Cell sum=a+b;
                v[block+j]=sum<prime?sum:sum-prime;
                v[block+j+step]=a>=b?a-b:a+prime-b;
            }
    }
};
void axis(std::vector<Cell>& data,int length,std::size_t stride,bool inverse) {
    Transform tr(length,inverse);
    std::vector<Cell> row(length);
    for(std::size_t group=0;group<data.size();group+=length*stride)
        for(std::size_t offset=0;offset<stride;++offset) {
            Cell* ptr=data.data()+group+offset;
            if(stride==1) tr.apply(ptr);
            else {
                for(int j=0;j<length;++j) row[j]=ptr[j*stride];
                tr.apply(row.data());
                for(int j=0;j<length;++j) ptr[j*stride]=row[j];
            }
        }
}
int best_half(const std::vector<int>& v) {
    int n=v.size(),total=0;
    for(int j=0;j<n/2;++j) total+=v[j];
    int best=total;
    for(int j=0;j<n-1;++j) {
        total+=v[(j+n/2)%n]-v[j]; best=std::max(best,total);
    }
    return best;
}
int main(int argc,char** argv) {
    if(argc!=4) return 2;
    int n=std::stoi(argv[1]),k=std::stoi(argv[2]);
    if(n<2 || n>=30000 || k<2 || k>=128) return 2;
    int nz=1;while(nz<2*k-1) nz*=2;
    int size=n*n;
    std::ifstream file(argv[3],std::ios::binary);
    std::vector<unsigned char> birth((std::istreambuf_iterator<char>(file)),{});
    if((int)birth.size()!=size) return 2;
    std::vector<Cell> data(std::size_t(size)*nz);
    Wide lower=0, distinct=0;
    for(int i=0;i<size;++i) if(birth[i]<k) {
        data[std::size_t(birth[i])*size+i]=1;
        lower+=k-birth[i]; ++distinct;
    }
    axis(data,n,1,false); axis(data,n,n,false); axis(data,nz,size,false);
    for(auto& x:data)x=times(x,x);
    axis(data,nz,size,true);axis(data,n,n,true);axis(data,n,1,true);
    Cell norm=power(data.size()%prime,prime-2);
    Wide pairCount=0;
    for(auto& x:data) {
        x=times(x,norm);
        // For a fixed sum and first occupied spatial square, the second square
        // and its birth layer are determined. Each coefficient is at most n².
        if(x>distinct)throw std::runtime_error("coefficient exceeds square count");
        pairCount+=x;
    }
    if(pairCount!=distinct*distinct)throw std::runtime_error("incorrect pair count");
    std::vector<bool> forbidden(size,false);
    std::vector<int> vals(n),columns(n);
    Wide upper=0;
    for(int h=0;h<k;++h) {
        for(int p=0;p<n;++p) for(int q=0;q<n;++q)
            if(data[std::size_t(h)*size+p*n+q]) {
                // An open unit square plus another covers all four neighboring
                // unit squares, up to the boundary lines omitted in the block.
                forbidden[p*n+q]=true;
                forbidden[((p+1)%n)*n+q]=true;
                forbidden[p*n+(q+1)%n]=true;
                forbidden[((p+1)%n)*n+(q+1)%n]=true;
            }
        for(int p=0;p<n;++p) {
            for(int q=0;q<n;++q) vals[q]=!forbidden[p*n+q];
            columns[p]=best_half(vals);
        }
        upper+=best_half(columns);
    }
    std::cout<<"lower "<<lower<<", upper "<<upper<<", distinct squares "<<distinct
             <<", ordered endpoint pairs "<<pairCount<<"\n";
    std::cout<<"volume numerator "<<2*lower+upper<<" denominator "<<Wide(4)*k*size<<"\n";
}
