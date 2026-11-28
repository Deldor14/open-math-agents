#include <iostream>
#include <vector>
#include <cstdint>
#include <cstdlib>
using Mask=uint32_t;
bool safe(Mask s, int L){
 for (int d=1;5*d<L;++d){
  Mask t=s & (s>>d);t &= t>>(2*d);if(t & ((s & (s>>d))>>(4*d)))return false;
 }return true;
}
int main(int argc,char**argv){
 int L=std::atoi(argv[1]), weight=std::atoi(argv[2]);Mask full=(1u<<L)-1;
 unsigned long long total=0;Mask zeros=(1u<<(L-weight))-1;
 while(zeros<=full){
  if(safe(full^zeros,L)){std::cout<<(full^zeros)<<"\n";++total;}
  Mask first=zeros&-zeros;Mask next=zeros+first;zeros=next|(((zeros^next)>>2)/first);
 }
 std::cerr<<L<<" "<<weight<<" "<<total<<"\n";
}
