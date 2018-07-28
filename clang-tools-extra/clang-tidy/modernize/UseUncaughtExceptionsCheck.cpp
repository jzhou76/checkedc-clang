//===--- UseUncaughtExceptionsCheck.cpp - clang-tidy--------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "UseUncaughtExceptionsCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"

using namespace clang::ast_matchers;

namespace clang {
namespace tidy {
namespace modernize {

void UseUncaughtExceptionsCheck::registerMatchers(MatchFinder *Finder) {
  if (!getLangOpts().CPlusPlus17)
    return;

  std::string MatchText = "::std::uncaught_exception";

  // Using declaration: warning and fix-it.
  Finder->addMatcher(
      usingDecl(hasAnyUsingShadowDecl(hasTargetDecl(hasName(MatchText))))
          .bind("using_decl"),
      this);

  // DeclRefExpr: warning, no fix-it.
  Finder->addMatcher(declRefExpr(allOf(to(functionDecl(hasName(MatchText))),
                                       unless(callExpr())))
                         .bind("decl_ref_expr"),
                     this);

  // CallExpr: warning, fix-it.
  Finder->addMatcher(
      callExpr(allOf(hasDeclaration(functionDecl(hasName(MatchText))),
                     unless(hasAncestor(initListExpr()))))
          .bind("call_expr"),
      this);
  // CallExpr in initialisation list: warning, fix-it with avoiding narrowing
  // conversions.
  Finder->addMatcher(
      callExpr(allOf(hasAncestor(initListExpr()),
                     hasDeclaration(functionDecl(hasName(MatchText)))))
          .bind("init_call_expr"),
      this);
}

void UseUncaughtExceptionsCheck::check(const MatchFinder::MatchResult &Result) {
  SourceLocation BeginLoc;
  SourceLocation EndLoc;
  const CallExpr *C = Result.Nodes.getNodeAs<CallExpr>("init_call_expr");
  bool WarnOnly = false;

  if (C) {
    BeginLoc = C->getLocStart();
    EndLoc = C->getLocEnd();
  } else if (const auto *E = Result.Nodes.getNodeAs<CallExpr>("call_expr")) {
    BeginLoc = E->getLocStart();
    EndLoc = E->getLocEnd();
  } else if (const auto *D =
                 Result.Nodes.getNodeAs<DeclRefExpr>("decl_ref_expr")) {
    BeginLoc = D->getLocStart();
    EndLoc = D->getLocEnd();
    WarnOnly = true;
  } else {
    const auto *U = Result.Nodes.getNodeAs<UsingDecl>("using_decl");
    assert(U && "Null pointer, no node provided");
    BeginLoc = U->getNameInfo().getBeginLoc();
    EndLoc = U->getNameInfo().getEndLoc();
  }

  auto Diag = diag(BeginLoc, "'std::uncaught_exception' is deprecated, use "
                             "'std::uncaught_exceptions' instead");

  if (!BeginLoc.isMacroID()) {
    StringRef Text =
        Lexer::getSourceText(CharSourceRange::getTokenRange(BeginLoc, EndLoc),
                             *Result.SourceManager, getLangOpts());

    Text.consume_back("()");
    int TextLength = Text.size();

    if (WarnOnly) {
      return;
    }

    if (!C) {
      Diag << FixItHint::CreateInsertion(BeginLoc.getLocWithOffset(TextLength),
                                         "s");
    } else {
      Diag << FixItHint::CreateReplacement(C->getSourceRange(),
                                           "std::uncaught_exceptions() > 0");
    }
  }
}

} // namespace modernize
} // namespace tidy
} // namespace clang