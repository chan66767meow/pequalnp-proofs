// Exact bounded mirror of the `search` and `optimized` definitions in
// https://github.com/open-goat/pequalnp-proofs/pull/17808 .
// This process produces search evidence only. Lean rechecks rejection.
#include <algorithm>
#include <array>
#include <chrono>
#include <csignal>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

using Word = uint64_t;
using State = std::vector<Word>;
constexpr Word Goal = 0xffffffff00000000ULL;
constexpr uint32_t AllCuts = 0xffffffffU;
volatile std::sig_atomic_t interrupted = 0;
void stop_signal(int) { interrupted = 1; }
struct BudgetEnd { const char* reason; };
struct Key {
  std::array<Word,12> words{};
  uint8_t fuel = 0, extra = 0, length = 0;
  bool operator==(const Key& b) const {
    return fuel==b.fuel && extra==b.extra && length==b.length && words==b.words;
  }
};
struct Hash {
  static uint64_t mix(uint64_t z) {
    z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;
    z=(z^(z>>27))*0x94d049bb133111ebULL;
    return z^(z>>31);
  }
  size_t operator()(const Key& k) const {
    uint64_t h=mix(k.fuel+17ULL*k.extra+257ULL*k.length);
    for(unsigned i=0;i<k.length;++i)h=mix(h^k.words[i]);
    return h;
  }
};
struct Engine {
  double seconds;
  uint64_t node_limit, nodes=0, memo_hits=0, branches=0, cut_rejections=0;
  size_t memo_limit=250000;
  std::chrono::steady_clock::time_point start=std::chrono::steady_clock::now();
  std::unordered_set<Key,Hash> rejected;
  Engine(double sec,uint64_t lim):seconds(sec),node_limit(lim){rejected.reserve(65536);}
  double elapsed() const {return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();}
  void budget(bool force=false) {
    if(interrupted)throw BudgetEnd{"interrupted"};
    if(nodes>=node_limit)throw BudgetEnd{"node_limit"};
    if((force||(nodes&2047)==0)&&elapsed()>=seconds)throw BudgetEnd{"time_limit"};
  }
  static uint32_t sep(Word x) {return static_cast<uint32_t>((x>>32)^x);}
  static uint32_t cuts(const State& ws) {uint32_t v=0;for(auto w:ws)v|=sep(w);return v;}
  bool run(unsigned fuel,unsigned extra,State ws) {
    ++nodes;budget();
    if(ws.size()==1&&(ws[0]==Goal||ws[0]==~Goal))return true;
    if(!fuel)return false;
    // Sorting is only a memoization canonicalization. All operations and
    // retention choices below are invariant under permutation, including when
    // a state contains duplicate signatures.
    std::sort(ws.begin(),ws.end());
    Key key;key.fuel=fuel;key.extra=extra;key.length=ws.size();
    std::copy(ws.begin(),ws.end(),key.words.begin());
    if(rejected.count(key)){++memo_hits;return false;}
    for(size_t i=0;i<ws.size();++i)for(size_t j=i+1;j<ws.size();++j){
      Word a=ws[i],b=ws[j];State rest;rest.reserve(ws.size());
      for(size_t t=0;t<ws.size();++t)if(t!=i&&t!=j)rest.push_back(ws[t]);
      uint32_t base=cuts(rest);
      const Word ops[4]={a&b,a|b,a&~b,b&~a};
      for(Word w:ops){
        uint32_t v=base|sep(w);
        for(unsigned keep=0;keep<4;++keep){
          unsigned charge=(keep&1)+((keep>>1)&1);
          if(charge>extra)continue;
          ++branches;
          uint32_t c=v;
          if(keep&1)c|=sep(a);
          if(keep&2)c|=sep(b);
          if(c!=AllCuts){++cut_rejections;continue;}
          State next=rest;next.push_back(w);
          if(keep&1)next.push_back(a);
          if(keep&2)next.push_back(b);
          if(run(fuel-1,extra-charge,std::move(next)))return true;
        }
      }
    }
    if(rejected.size()<memo_limit)rejected.insert(std::move(key));
    return false;
  }
  bool search(unsigned fuel,const State& inputs) {
    for(unsigned subset=0;subset<(1u<<inputs.size());++subset){
      budget(true);State ws;
      for(unsigned i=0;i<inputs.size();++i)if((subset>>i)&1)ws.push_back(inputs[i]);
      if(ws.size()>fuel+1||cuts(ws)!=AllCuts)continue;
      unsigned extra=fuel+1-ws.size();
      if(run(fuel,extra,std::move(ws)))return true;
    }
    return false;
  }
};
int main(int argc,char**argv){
  if(argc!=10){std::cerr<<"usage: sampled_binary_search BOUND SECONDS NODE_LIMIT MASK0 ... MASK5\n";return 2;}
  try{
    unsigned bound=std::stoul(argv[1]);double seconds=std::stod(argv[2]);uint64_t cap=std::stoull(argv[3]);
    if(bound>10||!(seconds>0&&seconds<=60)||!cap)throw std::invalid_argument("budget outside permitted range");
    State rows;for(int i=4;i<10;++i)rows.push_back(std::stoull(argv[i],nullptr,0));
    std::signal(SIGINT,stop_signal);std::signal(SIGTERM,stop_signal);
    Engine e(seconds,cap);std::string status;
    try{status=e.search(bound,rows)?"sample_feasible":"exhaustive_rejection";}
    catch(const BudgetEnd& end){status=end.reason;}
    std::cout<<"{\"status\":\""<<status<<"\",\"bound\":"<<bound
      <<",\"elapsed_seconds\":"<<e.elapsed()<<",\"nodes\":"<<e.nodes
      <<",\"branches\":"<<e.branches<<",\"cut_rejections\":"<<e.cut_rejections
      <<",\"memo_hits\":"<<e.memo_hits<<",\"memo_entries\":"<<e.rejected.size()<<"}\n";
    return 0;
  }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}
}
