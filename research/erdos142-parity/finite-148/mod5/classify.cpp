#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

using Word = uint64_t;
using Mask = uint32_t;
using Fibers = std::array<Mask,5>;
struct Rule { Fibers need{}; };

static std::vector<Rule> edges;
static int lengths[5], sparse, weight, target, n;
static std::vector<Mask> pool[5];
static Fibers chosen{};
static int order[4];
static std::vector<std::vector<Word>> missing;
static long long tuples, survivors, profiles;
static bool hit;
static std::vector<std::vector<int>> ruleId;
static bool within(Mask wanted,Mask selected) { return (wanted&selected)==wanted; }

static void fillSparse(Mask options,Mask used,int left){
 if(!left) {
  chosen[sparse]=used;
  for(const Rule& e:edges){
   bool complete=true;
   for(int i=0;i<5;i++) if(!within(e.need[i],chosen[i])) { complete=false;break; }
   if(complete)return;
  }
  hit=true;
  std::cout<<"FOUND";
  for(int x=1;x<=n;x++)if(chosen[(x-1)%5]>>((x-1)/5)&1U)std::cout<<' '<<x;
  std::cout<<std::endl;return;
 }
 while(!hit && __builtin_popcount(options)>=left) {
  Mask bit=options&-options;options^=bit;
  fillSparse(options,used|bit,left-1);
 }
}

static void finish(const std::vector<int>& live){
 int last=order[3], count=pool[last].size(), words=(count+63)/64;
 std::vector<Word> allowed(lengths[sparse]*words,~Word(0));
 for(int idx:live){
  const auto& rule=edges[idx].need;
  if(__builtin_popcount(rule[sparse])!=1)continue;
  int x=__builtin_ctz(rule[sparse]);
  const auto& ok=missing[ruleId[last][idx]];
  for(int w=0;w<words;w++)allowed[x*words+w]&=ok[w];
 }
 tuples+=count;
 for(int w=0;w<words && !hit;w++){
  Word bits[5]={};
  for(int x=0;x<lengths[sparse];x++){
   Word carry=allowed[x*words+w];
   for(int j=0;j<5;j++){Word next=bits[j]&carry;bits[j]^=carry;carry=next;}
  }
  Word qualifies=~Word(0);
  for(int j=0;j<5;j++){
   if((weight>>j)&1)qualifies&=bits[j];else qualifies|=bits[j];
  }
  if(w==words-1 && count%64)qualifies&=(Word(1)<<(count%64))-1;
  while(qualifies && !hit){
   int bit=__builtin_ctzll(qualifies);qualifies&=qualifies-1;
   ++survivors;Mask options=0;
   for(int x=0;x<lengths[sparse];x++)
    if((allowed[x*words+w]>>bit)&1)options|=1U<<x;
   chosen[last]=pool[last][64*w+bit];
   fillSparse(options,0,weight);
  }
 }
}

static void combine(int level,const std::vector<int>& live){
 if(level==3){finish(live);return;}
 int c=order[level];
 std::vector<int> next;next.reserve(live.size());
 for(Mask a:pool[c]){
  chosen[c]=a;next.clear();
  for(int idx:live)if(within(edges[idx].need[c],a))next.push_back(idx);
  combine(level+1,next);
  if(hit)return;
 }
}

static bool eligibleMask(Mask a,int length){
 for(int d=1;5*d<length;d++){
  Mask pair=a&(a>>d), four=pair&(pair>>(2*d));
  if(four&(pair>>(4*d)))return false;
 }
 return true;
}

static void solveProfile(const Fibers& sizes){
 for(int c=0,j=0;c<5;c++)if(c!=sparse){
  order[j++]=c;pool[c].clear();
  Mask full=(1U<<lengths[c])-1;
  int holes=lengths[c]-sizes[c];
  if(holes<=0 || holes>=lengths[c])std::abort();
  Mask omitted=(1U<<holes)-1;
  while(omitted<=full){
   Mask a=full^omitted;
   if(eligibleMask(a,lengths[c]))pool[c].push_back(a);
   Mask b=omitted&-omitted, next=omitted+b;
   omitted=next|(((next^omitted)>>2)/b);
  }
  if(pool[c].empty())return;
 }
 std::sort(order,order+4,[](int a,int b){return pool[a].size()<pool[b].size();});
 int c=order[3];int count=pool[c].size();int words=(count+63)/64;
 missing.clear();
 std::vector<std::pair<Mask,int>> seen;
 std::vector<int> live;
 for(size_t i=0;i<edges.size();i++){
  const auto& a=edges[i].need;
  if(!a[c] || !a[sparse])continue;
  live.push_back(i);
  if(__builtin_popcount(a[sparse])!=1)continue;
  int id=-1;
  for(auto record:seen)if(record.first==a[c]){id=record.second;break;}
  if(id<0){
   id=missing.size();seen.emplace_back(a[c],id);missing.emplace_back(words,0);
   for(int j=0;j<count;j++)
    if(!within(a[c],pool[c][j]))missing[id][j/64]|=Word(1)<<(j%64);
  }
  ruleId[c][i]=id;
 }
 ++profiles;
 combine(0,live);
}

static void enumerate(int c,int left,Fibers sizes){
 if(hit)return;
 if(c==5){if(left==0)solveProfile(sizes);return;}
 if(c==sparse){sizes[c]=weight;enumerate(c+1,left,sizes);return;}
 int maxSize=23;
 for(int deficit=0;deficit<=left;deficit++){
  sizes[c]=maxSize-deficit;enumerate(c+1,left-deficit,sizes);
 }
}

int main(int argc,char**argv){
 if(argc!=5)return 1;
 n=std::stoi(argv[1]);target=std::stoi(argv[2]);sparse=std::stoi(argv[3]);weight=std::stoi(argv[4]);
 if(n!=147 && n!=148)return 1;
 for(int i=0;i<n;i++)++lengths[i%5];
 for(int d=1;5*d<n;d++)for(int a=0;a+5*d<n;a++){
  Rule e;for(int j=0;j<6;j++){int x=a+j*d;e.need[x%5]|=1U<<(x/5);}
  edges.push_back(e);
 }
 ruleId.assign(5,std::vector<int>(edges.size(),-1));
 enumerate(0,4*23+weight-target,Fibers{});
 std::cout<<"n "<<n<<" target "<<target<<" indexed_class "<<sparse<<" occupancy "<<weight
  <<" profiles "<<profiles<<" tuples "<<tuples<<" passed_singleton_filter "<<survivors<<" found "<<hit<<std::endl;
}
