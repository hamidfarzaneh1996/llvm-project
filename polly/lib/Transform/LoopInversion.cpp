//===------ LoopInversion.cpp --------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Try to reduce the number of scatter dimension. Useful to make isl_union_map
// schedules more understandable. This is only intended for debugging and
// unittests, not for production use.
//
//===----------------------------------------------------------------------===//

#include "polly/LoopInversion.h"
#include "polly/InversionAlgo.h"
#include "polly/ScopInfo.h"
#include "polly/ScopPass.h"
#include "polly/Support/ISLOStream.h"
#include "polly/Support/ISLTools.h"
#define DEBUG_TYPE "polly-loop-inversion"

using namespace polly;
using namespace llvm;


namespace {

/// Print a schedule to @p OS.
///
/// Prints the schedule for each statements on a new line.
void printSchedule(raw_ostream &OS, const isl::union_map &Schedule,
                   int indent) {
  for (isl::map Map : Schedule.get_map_list())
    OS.indent(indent) << Map << "\n";
}

/// Flatten the schedule stored in an polly::Scop.
class LoopInversion : public ScopPass {
private:
  LoopInversion(const LoopInversion&) = delete;
  const LoopInversion &operator=(const LoopInversion &) = delete;

  std::shared_ptr<isl_ctx> IslCtx;
  isl::union_map OldSchedule;

public:
  static char ID;
  explicit LoopInversion() : ScopPass(ID) {}

  virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequiredTransitive<ScopInfoRegionPass>();
    AU.setPreservesAll();
  }

  virtual isl::union_pw_aff scheduleExtractDimAff(isl::union_map UMap, unsigned pos) {
    auto SingleUMap = isl::union_map::empty(UMap.get_space());
    for (isl::map Map : UMap.get_map_list()) {
      unsigned MapDims = Map.dim(isl::dim::out);
      isl::map SingleMap = Map.project_out(isl::dim::out, 0, pos);
      SingleMap = SingleMap.project_out(isl::dim::out, 1, MapDims - pos - 1);
      SingleUMap = SingleUMap.add_map(SingleMap);
    };

    auto UAff = isl::union_pw_multi_aff(SingleUMap);
    auto FirstMAff = isl::multi_union_pw_aff(UAff);
    return FirstMAff.get_union_pw_aff(0);
  }
  /// Compute @UPwAff * @p Val.
  isl::union_pw_aff multiply(isl::union_pw_aff UPwAff, isl::val Val) {
    if (Val.is_one())
      return UPwAff;

    auto Result = isl::union_pw_aff::empty(UPwAff.get_space());
    isl::stat Stat =
        UPwAff.foreach_pw_aff([=, &Result](isl::pw_aff PwAff) -> isl::stat {
          auto ValAff =
              isl::pw_aff(isl::set::universe(PwAff.get_space().domain()), Val);
          auto Multiplied = PwAff.mul(ValAff);
          Result = Result.union_add(Multiplied);
          return isl::stat::ok();
        });
    if (Stat.is_error())
      return {};
    return Result;
  }

  virtual bool runOnScop(Scop &S) override {
    // Keep a reference to isl_ctx to ensure that it is not freed before we free
    // OldSchedule.
    IslCtx = S.getSharedIslCtx();
    
    // S.setSchedule(S.getSchedule().reverse());
    LLVM_DEBUG(dbgs() << "Going to invert loop :\n");
    OldSchedule = S.getSchedule();
    LLVM_DEBUG(printSchedule(dbgs(), OldSchedule, 2));
    // auto Domains = isl::set(S.getDomains());
    // invertDomain(S.getSchedule());
    // auto newMap = isl::map::from_range(Domains);
    // newMap = newMap.neg();

    // auto newMap2 = isl::map::from_domain_and_range(newDomain, newMap.range());

    // OldSchedule = OldSchedule.from_range(newMap.range_map());
    auto Domains = S.getDomains();
    auto RestrictedOldSchedule = OldSchedule.intersect_domain(Domains);

    LLVM_DEBUG(dbgs() << "Old schedule :\n");
    LLVM_DEBUG(printSchedule(dbgs(), OldSchedule, 2));
    LLVM_DEBUG(dbgs() << "Restricted schedule :\n");
    LLVM_DEBUG(printSchedule(dbgs(), RestrictedOldSchedule, 2));
     
    auto range = OldSchedule.range();
    LLVM_DEBUG(dbgs() << "range :\n" << range << "\n");

    auto range1 = RestrictedOldSchedule.range();
    LLVM_DEBUG(dbgs() << "range1 :\n" << range1 << "\n");

    auto range1_set = isl::set(range1);
    LLVM_DEBUG(dbgs() << "range1_set :\n" << range1_set << "\n");

    auto range1_set_neg = range1_set.neg();
    LLVM_DEBUG(dbgs() << "range1_set_neg :\n" << range1_set_neg << "\n");

    auto range1_neg_flatten = range1_set_neg.flatten_map();
    LLVM_DEBUG(dbgs() << "range1_neg_flatten :\n" << range1_neg_flatten<< "\n");

    LLVM_DEBUG(dbgs() << "Restricted schedule :\n");
    LLVM_DEBUG(printSchedule(dbgs(), RestrictedOldSchedule, 2));

    auto range_map = RestrictedOldSchedule.range_map();
    LLVM_DEBUG(dbgs() << "range map :\n" << range_map << "\n");
    
    auto domain_map = RestrictedOldSchedule.domain_map();
    LLVM_DEBUG(dbgs() << "domain map :\n" << domain_map << "\n");

    LLVM_DEBUG(dbgs() << "domain map 2 :\n" << domain_map.domain() << "\n");

    auto range_map_domain = range_map.domain(); 
    LLVM_DEBUG(dbgs() << "range map domain:\n" << range_map_domain << "\n");
    
    auto range_map_negated = range_map.from_range(range1_set_neg);
    LLVM_DEBUG(dbgs() << "range map negated:\n" << range_map_negated << "\n");

    auto range_map_negated_with_domain = range_map.flat_range_product(range_map_negated);
    LLVM_DEBUG(dbgs() << "range map negated:\n" << range_map_negated << "\n");

    auto extracted1 = scheduleExtractDimAff(RestrictedOldSchedule, 0);
    LLVM_DEBUG(dbgs() << "extracted 1:\n" << extracted1<< "\n");

    auto extracted1_neg = extracted1.neg();
    LLVM_DEBUG(dbgs() << "extracted 1 neg:\n" << extracted1_neg<< "\n");

    auto IndexMap = isl::union_map(extracted1_neg);
    auto Min = range1_set.dim_min(0);
    auto MinVal = getConstant(Min, false, true);
    auto LenVal = MinVal.sub(MinVal).sub_ui(1);
    auto Offset = multiply(extracted1, LenVal);
    LLVM_DEBUG(dbgs() << "Multiplied extracted :\n  " << Offset << "\n");
    auto MultipliedMap = isl::union_map(Offset);
    LLVM_DEBUG(dbgs() << "Multiplied map :\n  " << MultipliedMap << "\n");

    auto AllDomains = MultipliedMap.domain();
    LLVM_DEBUG(dbgs() << "AllDomain:\n  " << AllDomains<< "\n");
    auto AllDomainsToNull = isl::union_pw_multi_aff(range1_set_neg);
    LLVM_DEBUG(dbgs() << "AllDomainsToNull:\n  " << AllDomainsToNull<< "\n");

    auto removedDomains = isl::union_pw_multi_aff(AllDomains);
    auto removedRange = isl::union_pw_multi_aff(range1_neg_flatten);


    auto test_map1 = isl::map::empty(RestrictedOldSchedule.get_space()).from_domain(isl::set(domain_map.domain()));
    LLVM_DEBUG(dbgs() << "test map1 :\n" << test_map1 << "\n");

    auto test_map2 = isl::map::empty(RestrictedOldSchedule.get_space()).from_range(isl::set(domain_map.domain()));
    LLVM_DEBUG(dbgs() << "test map2 :\n" << test_map2 << "\n");

    auto test_map3 = isl::map::empty(RestrictedOldSchedule.get_space()).from_domain_and_range(isl::set(domain_map.domain()), isl::set(range1_set_neg));
    LLVM_DEBUG(dbgs() << "test map3 :\n" << test_map3 << "\n");

    auto test_map4 = isl::map::empty(RestrictedOldSchedule.get_space()).from_domain_and_range( isl::set(range1_set_neg), isl::set(domain_map.domain()));
    LLVM_DEBUG(dbgs() << "test map4 :\n" << test_map4 << "\n");

    auto test_map5 = isl::map::empty(RestrictedOldSchedule.get_space()).from_range( isl::set(range1_set_neg));
    LLVM_DEBUG(dbgs() << "test map5 :\n" << test_map5 << "\n");

    auto test_map6 = isl::map::empty(RestrictedOldSchedule.get_space()).from_domain_and_range( isl::set(range1_set_neg), isl::set(AllDomainsToNull.domain()));
    LLVM_DEBUG(dbgs() << "test map6 :\n" << test_map6 << "\n");

    auto test_map7 = isl::map::empty(RestrictedOldSchedule.get_space()).from_domain_and_range(isl::set(removedDomains.domain()), isl::set(range1_set_neg) );
    LLVM_DEBUG(dbgs() << "test map7 :\n" << test_map7 << "\n");

    auto test_map8 = isl::map::from_range(range1_set_neg);
    LLVM_DEBUG(dbgs() << "test map8 :\n" << test_map8 << "\n");

    auto neg_map = isl::union_map(extracted1_neg);
    
    auto test_map9 = isl::map::from_domain_and_range(isl::set(extracted1_neg.domain()),range1_set);
    
    LLVM_DEBUG(dbgs() << "test_map9:\n  " << test_map9<< "\n");

    auto test_map10 = isl::union_map(test_map7).gist_domain(Domains);
    LLVM_DEBUG(dbgs() << "test_map10:\n  " << test_map10<< "\n");
    auto test_map11 = isl::union_map(test_map7).gist(RestrictedOldSchedule);
    LLVM_DEBUG(dbgs() << "test_map11:\n  " << test_map11<< "\n");


    auto map2 = IndexMap.apply_range(isl::union_map(range1_set_neg.flatten_map()));
    LLVM_DEBUG(dbgs() << "map2:\n  " << map2<< "\n");

    auto map3 = map2.apply_domain(isl::union_map(range1_set_neg.flatten_map()));
    LLVM_DEBUG(dbgs() << "map3:\n  " << map3<< "\n");

    auto map4 = map3.apply_range(isl::union_map(range1_set_neg.flatten_map()));
    LLVM_DEBUG(dbgs() << "map4:\n  " << map4<< "\n");

    auto map5 = range_map_negated_with_domain.apply_range(map2);
    LLVM_DEBUG(dbgs() << "map5:\n  " << map5<< "\n");

    auto test_map12 = isl::union_map::from_domain_and_range(range1_set_neg,map2.range());
    LLVM_DEBUG(dbgs() << "test_map12:\n  " << test_map12<< "\n");

    auto test_map13 = isl::union_map::from_domain_and_range(map2.range(), range1_set_neg);
    LLVM_DEBUG(dbgs() << "test_map13:\n  " << test_map13<< "\n");

    auto test_map14 = isl::union_map::from_domain_and_range(range1_set_neg.neg(),map2.domain());
    LLVM_DEBUG(dbgs() << "test_map14:\n  " << test_map14<< "\n");

    auto test_map15 = isl::union_map::from_domain_and_range(RestrictedOldSchedule.range(), range1_set_neg);
    LLVM_DEBUG(dbgs() << "test_map15:\n  " << test_map15<< "\n");

    auto test_map16 = test_map15.gist(RestrictedOldSchedule);
    LLVM_DEBUG(dbgs() << "test_map16:\n  " << test_map16<< "\n");

    auto test_map17 = RestrictedOldSchedule.gist_range(range1_set_neg);
    LLVM_DEBUG(dbgs() << "test_map17:\n  " << test_map17<< "\n");




    // auto ScheduleWithOffset = isl::union_map(AllDomainsToNull).from_domain_and_range
    //   (AllDomainsToNull,AllDomainsToNull)
                    
    // LLVM_DEBUG(dbgs() << "ScheduleWithOffset:\n  " << ScheduleWithOffset<< "\n");
    S.setSchedule(IndexMap);
    // S.setSchedule(range1_neg_flatten);
    // S.setSchedule(test_map10);

    

    // auto map4 = map2.apply_domain(isl::union_map(range1));
    // LLVM_DEBUG(dbgs() << "map4:\n  " << map4<< "\n");


    // auto range_map2 = range_map.reverse(); // not usefule at all
    // LLVM_DEBUG(dbgs() << "range map2 (reverese):\n" << range_map2 << "\n");

    // auto domain = RestrictedOldSchedule.domain();
    // LLVM_DEBUG(dbgs() << "domain :\n" << domain << "\n");
    

    // auto domain_map = RestrictedOldSchedule.domain_map();
    // LLVM_DEBUG(dbgs() << "domain_map :\n" << domain_map<< "\n");
    

    // auto params = RestrictedOldSchedule.params();
    // LLVM_DEBUG(dbgs() << "params :\n" << params << "\n");


    // OldSchedule = OldSchedule.apply_domain(newMap2);
    

    // // auto RestrictedOldSchedule = OldSchedule.intersect(newMap);
    // // auto RestrictedOldSchedule = OldSchedule.intersect_domain(Domains);
    // LLVM_DEBUG(dbgs() << "new map:\n");
    // LLVM_DEBUG(dbgs() << newMap);
    // LLVM_DEBUG(dbgs() << "new map:\n");
    // LLVM_DEBUG(dbgs() << newMap2);
    // LLVM_DEBUG(dbgs() << "Old schedule with domains:\n");
    // LLVM_DEBUG(printSchedule(dbgs(), OldSchedule, 2));
    // LLVM_DEBUG(printSchedule(dbgs(), RestrictedOldSchedule, 2));

    // auto NewSchedule = invertLoop(RestrictedOldSchedule);

    // LLVM_DEBUG(dbgs() << "inverted new schedule:\n");
    // LLVM_DEBUG(printSchedule(dbgs(), NewSchedule, 2));
    // S.setDomain(EntryBB, invertDomain(RestrictedOldSchedule));


    // NewSchedule = NewSchedule.gist_domain(Domains);
    // LLVM_DEBUG(dbgs() << "Gisted, inverted schedule:\n");
    // LLVM_DEBUG(printSchedule(dbgs(), NewSchedule, 2));

    // S.setSchedule(NewSchedule);
    // S.setSchedule(newMap);
    return false;
  }

  virtual void printScop(raw_ostream &OS, Scop &S) const override {
    OS << "Schedule before inverting {\n";
    printSchedule(OS, OldSchedule, 4);
    OS << "}\n\n";

    OS << "Schedule after inverting {\n";
    printSchedule(OS, S.getSchedule(), 4);
    OS << "}\n";
  }

  virtual void releaseMemory() override {
    OldSchedule = nullptr;
    IslCtx.reset();
  }
};

char LoopInversion::ID;
} // anonymous namespace

Pass *polly::createLoopInversionPass() { return new LoopInversion(); }

INITIALIZE_PASS_BEGIN(LoopInversion, "polly-loop-inversion",
                      "Polly - Loop Inversion", false, false)
INITIALIZE_PASS_END(LoopInversion, "polly-loop-inversion",
                    "Polly - Loop Inversion", false, false)
