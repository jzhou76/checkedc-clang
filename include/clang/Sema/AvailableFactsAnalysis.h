//===-------- AvailableFactsAnalysis.h - collect comparison facts --------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines the interface for performing an analysis for collecting 
//  comparison facts.
//
//  The analysis has the following characteristics: 1. forward dataflow analysis,
//  2. conservative, 3. intra-procedural, and 4. path-sensitive.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_AVAILABLE_FACTS_ANALYSIS_H
#define LLVM_AVAILABLE_FACTS_ANALYSIS_H

#include "clang/Analysis/CFG.h"
#include "clang/Analysis/Analyses/PostOrderCFGView.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "clang/Sema/Sema.h"
#include <queue>

namespace clang {
  using Comparison = std::pair<Expr *, Expr *>;
  using ComparisonSet = std::set<Comparison>;

  class AvailableFactsAnalysis {
    class ElevatedCFGBlock;

  private:
    Sema &S;
    CFG *Cfg;
    bool DumpFacts;
    std::vector<ElevatedCFGBlock *> Blocks;
    std::vector<unsigned int> BlockIDs;
    std::size_t CurrentIndex;
    std::queue<ElevatedCFGBlock *> WorkList;

    class ElevatedCFGBlock {
    private:
      const CFGBlock *Block;
      ComparisonSet In, OutThen, OutElse;
      ComparisonSet Kill, GenThen, GenElse;

    public:
      ElevatedCFGBlock(const CFGBlock *Block) : Block(Block) {}

      friend class AvailableFactsAnalysis;
    };

  public:
    AvailableFactsAnalysis(Sema &S, CFG *Cfg) : S(S), Cfg(Cfg), CurrentIndex(0),
                                                DumpFacts(S.getLangOpts().DumpExtractedComparisonFacts) {}

    void Analyze();
    void Reset();
    void Next();
    void GetFacts(std::set<std::pair<Expr *, Expr *>>& ComparisonFacts);
  
  private:
    ElevatedCFGBlock* GetByCFGBlock(const CFGBlock *B);
    ComparisonSet Difference(ComparisonSet& S1, ComparisonSet& S2);
    ComparisonSet Union(ComparisonSet& S1, ComparisonSet& S2);
    bool Differ(ComparisonSet& S1, ComparisonSet& S2);
    ComparisonSet Intersect(ComparisonSet& S1, ComparisonSet& S2);
    bool ContainsVariable(Comparison& I, const VarDecl *V);
    void ExtractComparisons(const Expr *E, ComparisonSet &ISet);
    void ExtractNegatedComparisons(const Expr *E, ComparisonSet &ISet);
    void CollectExpressions(const Stmt *St, std::set<const Expr *> &AllExprs);
    void CollectDefinedVars(const Stmt *St, std::set<const VarDecl *> &DefinedVars);
    void PrintComparisonSet(raw_ostream &OS, ComparisonSet &ISet, std::string Title);
    void DumpComparisonFacts(raw_ostream &OS);
  };
}

#endif
