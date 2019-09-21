//== SimpleBoundsChecker.cpp ------------------------------*- C++ -*--==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines SimpleBoundsChecker, which is a path-sensitive check
// which looks for an out-of-bound accesses.
//
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"

#include <string>

#define DEBUG_DUMP 1

using namespace clang;
using namespace ento;

namespace {
    // struct BoundsState
    // {
    //     void Profile(llvm::FoldingSetNodeID &ID) const {
    //         ID.AddInteger(K);
    //     }
    // };
    class SimpleBoundsChecker :
        public Checker<check::Location,
                    check::BeginFunction> {
    mutable std::unique_ptr<BuiltinBug> BT;

    void checkBoundsInfo(const DeclaratorDecl* decl, std::string label, ASTContext& Ctx) const;

    public:
    void checkLocation(SVal l, bool isLoad, const Stmt* S,
                        CheckerContext &C) const;
    void checkBeginFunction(CheckerContext& C) const;
    };
}

REGISTER_MAP_WITH_PROGRAMSTATE(BoundsMap, SymbolRef, SymbolRef)

void SimpleBoundsChecker::checkLocation(SVal l, bool isLoad, const Stmt* LoadS,
                                      CheckerContext &C) const {
    // Check for out of bound element accesses
    const MemRegion *R = l.getAsRegion();
    if (!R)
    return;

    //  LoadS->dump();
    //  fprintf(stderr, "DBG: checkLocation (isLoad: %d)\n", isLoad);


    const ElementRegion *ER = dyn_cast<ElementRegion>(R);
    if (!ER)
    return;

    // Get the index of the accessed element.
    DefinedOrUnknownSVal Idx = ER->getIndex().castAs<DefinedOrUnknownSVal>();

    bool bugFound = false;

    #ifdef BOUNDS_CHECK_WITH_Z3
    // For handling complex expression over indices:
    // 1. Create a Z3 instance
    SMTSolverRef solver = CreateZ3Solver();

    // 2. Read the Symbolic expr of the index
    //    it should be of the form: (idx < lower_bound) v (idx > upper_bound)
    //
    // TODO

    // 3. pass it to Z3
    Optional<bool> isSat = solver->check();
    if ( isSat.hasValue() ) {
        if ( !isSat.getValue() )
        return;
        
    // 4. [Optional] Read the model. The model represents a possible input
    //               value that makes the index go out of bounds
    // TODO
    bugFound = true;
    }

    #else

    // Zero index is always in bound, this also passes ElementRegions created for
    // pointer casts.
    if (Idx.isZeroConstant())
    return;

    ProgramStateRef state = C.getState();

    // Get the size of the array.
    DefinedOrUnknownSVal NumElements
    = C.getStoreManager().getSizeInElements(state, ER->getSuperRegion(),
                                            ER->getValueType());

    ProgramStateRef StInBound = state->assumeInBound(Idx, NumElements, true);
    ProgramStateRef StOutBound = state->assumeInBound(Idx, NumElements, false);
    bugFound = (StOutBound && !StInBound);

    #endif

    if ( bugFound ) {
    ExplodedNode *N = C.generateErrorNode(StOutBound);
    if (!N)
        return;

    if (!BT)
        BT.reset(new BuiltinBug(
            this, "Out-of-bound array access",
            "Access out-of-bound array element (buffer overflow)"));

    // Generate a report for this bug.
    auto report = llvm::make_unique<BugReport>(*BT, BT->getDescription(), N);

    report->addRange(LoadS->getSourceRange());
    C.emitReport(std::move(report));
    return;
    }

    // Array bound check succeeded.  From this point forward the array bound
    // should always succeed.
    C.addTransition(StInBound);
}

void SimpleBoundsChecker::checkBoundsInfo(const DeclaratorDecl* decl, std::string label, ASTContext& Ctx) const {
    llvm::errs() << "Processing: " << label << " ( " << decl->getDeclName() << " )\n";

    //decl->dump();

    if ( decl->hasBoundsSafeInterface(Ctx) )
        llvm::errs() << "Bounds-safe interface *found*!\n";
    else
        llvm::errs() << "Bounds-safe interface not found!\n";

    if ( decl->hasBoundsDeclaration(Ctx) )
        llvm::errs() << "Bounds declaration *found*!\n";
    else
        llvm::errs() << "Bounds declaration not found!\n";


    const BoundsExpr* BE = decl->getBoundsExpr();
    if (!BE) llvm::errs() << "BoundsExpr is NULL\n";
    else { llvm::errs() << "BoundsExpr: \n"; BE->dumpColor(); }

    const InteropTypeExpr* IE = decl->getInteropTypeExpr();
    if (!IE) llvm::errs() << "InteropTypeExpr is NULL\n";
    else { llvm::errs() << "InteropExpr: \n"; IE->dumpColor(); }
}

void SimpleBoundsChecker::checkBeginFunction(CheckerContext& C) const {
    ProgramStateRef state = C.getState();
    ProgramStateManager &SM = state->getStateManager();
    SValBuilder &svalBuilder = SM.getSValBuilder();
    ASTContext &Ctx = svalBuilder.getContext();

    const LocationContext *LCtx = C.getLocationContext();
    const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(LCtx->getDecl());
    if (!FD)
        return;
    
    FD = FD->getCanonicalDecl();

#ifdef DEBUG_DUMP
    checkBoundsInfo(FD, "function", Ctx);
    for( unsigned int i=0; i<FD->getNumParams(); i++ ) {
        const ParmVarDecl* arg = FD->getParamDecl(i);
        checkBoundsInfo(arg, "arg" + std::to_string(i), Ctx);
    }
#endif

    const ParmVarDecl* arg0 = FD->getParamDecl(0);
    Loc argLoc = svalBuilder.makeLoc(state->getRegion(arg0, LCtx));
    SVal argSVal = state->getSVal(argLoc);

    const CountBoundsExpr* CBE = dyn_cast<CountBoundsExpr>(arg0->getBoundsExpr());
    SVal argBoundSVal = C.getSVal(CBE->getCountExpr());

    state = state->set<BoundsMap>(argSVal.getAsSymbolicExpression(), argBoundSVal.getAsSymbolicExpression());
    C.addTransition(state);




    // TODO
    // Q: How can I read the bounds-safe information here?
    // he "InteropTypeExpr" class is used for describing the interface expression
    //
    // in the ExprEngine::Visit, it is assumed that the static analyzer does not know about the Checked-C extensions:
    // see line 1798 of lib/StaticAnalyzer/Core/ExprEngine.cpp
    // Q: Is it only for case-by-case expression type handling?

    // Q: after reading the bounds should we push it to ProgramState (to be read by checkLocation) or put it as the memRegion's extent?


    //const MemRegion* R = state->getRegion(FD->getParamDecl(0), LCtx);
    //if (!R)
    //    return;
    
}

void ento::registerSimpleBoundsChecker(CheckerManager &mgr) {
  mgr.registerChecker<SimpleBoundsChecker>();
}
