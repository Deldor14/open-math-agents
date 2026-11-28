#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
using namespace std;
using Mask = unsigned __int128;
static int cap[150],k,n,target,bound[100],batch,batchbits;
static uint64_t countNodes,countSets;
static Mask full,small[100],lines[9][9],previous[100][32];
static int len[9][9],dc[100];
static int pop(Mask m){return __builtin_popcountll((uint64_t)m)+__builtin_popcountll((uint64_t)(m>>64));}
void visit(int pos,int used,Mask selected,Mask forbidden){
 ++countNodes;
 if(used==target){
  ++countSets;cout<<hex<<(uint64_t)(selected>>64)<<' '<<(uint64_t)selected<<dec<<'\n';return;
 }
 if(pos==n||used+bound[n-pos]<target)return;
 Mask available=full&~small[pos]&~forbidden;
 if(used+pop(available)<target)return;
 if(pos%4==0){
  for(int d=2;d<=7;d++){
   int mx=used;
   for(int r=0;r<d;r++){
    Mask v=lines[d][r];
    int a=pop(v&small[pos]), u=pop(v&selected),f=pop(v&available);
    mx+=min({f,cap[len[d][r]]-u,cap[len[d][r]-a]});
   }
   if(mx<target)return;
  }
 }
 bool allow=available>>pos&1;
 bool after=pos>=batchbits,choice=(batch>>pos%30)&1;
 if(allow&&(after||choice)){
  Mask next=selected|(Mask(1)<<pos);
  bool good=true;
  for(int l=6;l<=pos+1;l++)
   if(cap[l]==cap[l-1] && pop(next&(small[pos+1]^small[pos+1-l]))>cap[l]){good=false;break;}
  if(good){
   Mask forbid=forbidden;
   for(int d=1;d<=dc[pos];d++)if((selected&previous[pos][d])==previous[pos][d])forbid|=Mask(1)<<(pos+d);
   visit(pos+1,used+1,next,forbid);
  }
 }
 if(after||!choice)visit(pos+1,used,selected,forbidden);
}
int main(int argc,char**argv){
 k=atoi(argv[1]);n=atoi(argv[2]);target=atoi(argv[3]);batchbits=atoi(argv[4]);batch=atoi(argv[5]);
 ifstream f(argv[6]);int a,b; while(f>>a>>b)cap[a]=b;
 full=(Mask(1)<<n)-1;
 for(int i=0;i<=n;i++){small[i]=(Mask(1)<<i)-1;bound[i]=cap[i];}
 for(int d=2;d<=7;d++)for(int x=0;x<n;x++){lines[d][x%d]|=Mask(1)<<x;len[d][x%d]++;}
 for(int x=0;x<n;x++){dc[x]=min(x/(k-2),n-1-x);for(int d=1;d<=dc[x];d++)for(int j=1;j<=k-2;j++)previous[x][d]|=Mask(1)<<(x-j*d);}
 visit(0,0,0,0);cerr<<"visited "<<countNodes<<" sets "<<countSets<<" completed"<<endl;
}
