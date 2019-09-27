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
#include "clang/StaticAnalyzer/Core/PathSensitive/SMTConv.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SMTSolver.h"


#include <string>

#define DEBUG_DUMP true
#define BOUNDS_CHECK_WITH_Z3 true
#define TEST_PROGRAM_STATE false
#define USE_PROGRAM_STATE false

using namespace clang;
using namespace ento;

namespace {
#if TEST_PROGRAM_STATE
    struct BoundsState
    {
        private:
        int K;
        BoundsState(int k) : K(k) {}

        public:
        bool isZero() const { return K == 0; }
        bool isOne() const {return K == 1;}

        static BoundsState mkZeroBoundsState() { return BoundsState(0); }
        static BoundsState mkOneBoundsState() { return BoundsState(1); }

        bool operator==(const BoundsState &X) const {
            return K == X.K;
        }

        void Profile(llvm::FoldingSetNodeID &ID) const {
            ID.AddInteger(K);
        }
    };
#endif

    class SimpleBoundsChecker : public Checker<check::Location,
                                               check::BeginFunction> {
        mutable std::unique_ptr<BuiltinBug> BT;

        void checkBoundsInfo(const DeclaratorDecl* decl, std::string label, ASTContext& Ctx) const;

    public:
        void checkLocation(SVal l, bool isLoad, const Stmt* S,
                            CheckerContext &C) const;
        void checkBeginFunction(CheckerContext& C) const;
    };
}

#if TEST_PROGRAM_STATE
REGISTER_MAP_WITH_PROGRAMSTATE(BoundsMap, SymbolRef, BoundsState)
#else
REGISTER_MAP_WITH_PROGRAMSTATE(BoundsMap, SymbolRef, SymbolRef)
#endif

void SimpleBoundsChecker::checkLocation(SVal l, bool isLoad, const Stmt* LoadS,
                                      CheckerContext &C) const {

    const MemRegion *R = l.getAsRegion();
    if (!R)
        return;

    const ElementRegion *ER = dyn_cast<ElementRegion>(R);
    if (!ER)
        return;

    // Only load statements of array subscript type should reach this point.

#if DEBUG_DUMP
    llvm::errs() << "\nLoad Statement:\n";
    LoadS->dumpColor();
    const ArraySubscriptExpr* ASE = dyn_cast<ArraySubscriptExpr>(LoadS);
    if (!ASE){
        llvm::errs() << "Load statement is not an array subscript expression!\n";
        return;
    }
    const Expr* arrayBase = ASE->getBase();
    llvm::errs() << "\nArray base:\n";
    arrayBase->dumpColor();
#endif


    ProgramStateRef state = C.getState();
    ProgramStateManager &SM = state->getStateManager();
    SValBuilder &svalBuilder = SM.getSValBuilder();
    ASTContext &Ctx = svalBuilder.getContext();
    


    // Get the index of the accessed element.
    DefinedOrUnknownSVal Idx = ER->getIndex().castAs<DefinedOrUnknownSVal>();

    if (Idx.isZeroConstant())
        return;

    // Get the size of the array.
    DefinedOrUnknownSVal NumElements = C.getStoreManager().getSizeInElements(state, ER->getSuperRegion(), ER->getValueType());

    ProgramStateRef StInBound = state->assumeInBound(Idx, NumElements, true);
    ProgramStateRef StOutBound = state->assumeInBound(Idx, NumElements, false);

    bool bugFound = false;

#if BOUNDS_CHECK_WITH_Z3
    // For handling complex expressions over indices:
    // 1. Create a Z3 instance
    SMTSolverRef solver = CreateZ3Solver();

    // 2. Read the Symbolic expr of the index
    //
    Loc arrLoc = svalBuilder.makeLoc(ER->getBaseRegion());
    SVal arrLocSVal = state->getSVal(arrLoc);

    SymbolRef AR =  arrLocSVal.getAsSymbolicExpression();
    if (!AR) {
        llvm::errs() << "AR is NULL\n";
        return;
    }

#if DEBUG_DUMP
    llvm::errs() << "\nArray location sym expr:\n";
    AR->dump();

    MemRegion::Kind K = ER->getSuperRegion()->getKind();
    llvm::errs() << "\ncheckLoc: memreg.kind: " << K << "\n";
#endif

#if TEST_PROGRAM_STATE
    const BoundsState* BS = state->get<BoundsMap>(AR);
    if (!BS) {
        llvm::errs() << "BS is NULL!\n";
    }
    else {
        llvm::errs() << "Read BoundsState: isZero(" << BS->isZero() << "), isOne(" << BS->isOne() << ")\n";
    }
#endif

#if USE_PROGRAM_STATE    
    const SymbolRef* _SR = state->get<BoundsMap>(AR);
    if (!_SR) {
       llvm::errs() << "\n_SR is NULL\n";
       return;
    }
    SymbolRef SR = *_SR;
#endif

#if !USE_PROGRAM_STATE
    const LocationContext *LCtx = C.getLocationContext();
    const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(LCtx->getDecl());
    //SymbolRef BoundsSym;
    if (!FD) {
        llvm::errs() << "FD in checkLoc is NULL!\n";
    }
    else {
        FD = FD->getCanonicalDecl();
        const ParmVarDecl* arg = FD->getParamDecl(0);
        //checkBoundsInfo(arg, "checkLoc::argument", Ctx);
        const CountBoundsExpr* CBE = dyn_cast<CountBoundsExpr>(arg->getBoundsExpr());
        CBE->dumpColor();

        //SVal argBoundSVal = C.getSVal(CBE->getCountExpr());
        //BoundsSym = argBoundSVal.getAsSymbolicExpression();

        /* DEBUG START */
        /* These are debug codes, attempting to get to the ParmVar inside the CountBoundsExpr */
        const DeclRefExpr* t = dyn_cast<DeclRefExpr>(arg->getBoundsExpr());
        if (!t) {llvm::errs() << "t is NULL!"; }
        const ImplicitCastExpr* ICE = dyn_cast<ImplicitCastExpr>(CBE);
        if (!ICE) {
            llvm::errs() << "ICE is NULL!\n";
            const DeclRefExpr* DRE = dyn_cast<DeclRefExpr>(CBE);
            if (!DRE)
                llvm::errs() << "DRE is NULL!\n";
            else
            {
                DRE->dumpColor();
                llvm::errs() << DRE->getDecl()->getName() << "\n";
            }
        }
        else {
            const DeclRefExpr* DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr());
            llvm::errs() << "-- DRE --\n";
            DRE->dumpColor();
            llvm::errs() << DRE->getDecl()->getName() << "\n";
        }
        /* DEBUG END */
    }
#endif


    // 3. Encode the expression as a SMT formula
    //    it should be of the form: (idx < lower_bound) v (idx > upper_bound)
    //
    // TODO: currently only expressions of count(n) is handled, generalize for bounds(LB, UB)
    //
    // SMT expression of the bounds expression
    SMTExprRef BE = SMTConv::getExpr(solver, Ctx, AR);
    // SMT expression of the index
    SMTExprRef idx = SMTConv::getExpr(solver, Ctx, Idx.getAsSymbol());
    // SMT expression for (idx > UpperBound)
    SMTExprRef overUB = solver->mkBVUgt(idx, BE);
    // SMT expression for (idx < LowerBound)
    SMTExprRef underLB = solver->mkBVUlt(idx, solver->mkBitvector(llvm::APSInt(32), 32));
    
    // the final SMT expression
    SMTExprRef constraint = solver->mkOr(underLB, overUB); constraint->print(llvm::errs()); llvm::errs() << "\n";

    solver->addConstraint(constraint);

    // 4. Solve the SMT formula for a bad input using Z3
    Optional<bool> isSat = solver->check();
    if ( isSat.hasValue() ) {
        if ( !isSat.getValue() ) // If the formula is UNSAT, there is no input value that makes the index go out-of-bounds
            return;

        bugFound = true;
    }
    // 5. [Optional] Read the model. The model represents a possible input
    //               value that makes the index go out of bounds.
    //               Only useful for bug reports and debugging!

#else

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
        llvm::errs() << "    Bounds-safe interface *found*!\n";
    else
        llvm::errs() << "    Bounds-safe interface not found!\n";

    if ( decl->hasBoundsDeclaration(Ctx) )
        llvm::errs() << "    Bounds declaration *found*!\n";
    else
        llvm::errs() << "    Bounds declaration not found!\n";


    const BoundsExpr* BE = decl->getBoundsExpr();
    if (BE) { llvm::errs() << "    BoundsExpr: \n"; BE->dumpColor(); }

    const InteropTypeExpr* IE = decl->getInteropTypeExpr();
    if (IE) { llvm::errs() << "    InteropExpr: \n"; IE->dumpColor(); }
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

    CheckedScopeSpecifier CSS = FD->getCheckedSpecifier();
    if ( CSS == CSS_Bounds || CSS == CSS_Memory ) {
        #if DEBUG_DUMP
        llvm::errs() << "Skipping the function " << FD->getDeclName() << ". Because it is in Checked scope!\n";
        #endif
        return;
    }

    bool hasBoundsDecl = FD->hasBoundsDeclaration(Ctx);
    bool hasBoundsSafeDecl = FD->hasBoundsSafeInterface(Ctx);
    for( unsigned int i=0; i<FD->getNumParams(); i++ ) {
        const ParmVarDecl* arg = FD->getParamDecl(i);
        hasBoundsDecl = hasBoundsDecl || arg->hasBoundsDeclaration(Ctx);
        hasBoundsSafeDecl = hasBoundsSafeDecl || arg->hasBoundsSafeInterface(Ctx);
    }

    // If the function has bounds declaration then it is not a bounds-safe interface!
    if ( hasBoundsDecl ) {
        #if DEBUG_DUMP
        llvm::errs() << "Skipping the function " << FD->getDeclName() << ". Because it has bounds declaration!\n";
        #endif
        return;
    }

    if ( !hasBoundsSafeDecl ) {
        #if DEBUG_DUMP
        llvm::errs() << "Skipping the function " << FD->getDeclName() << ". Because it doesn't have bounds-safe information!\n";
        #endif
        return;
    }


#if DEBUG_DUMP
    checkBoundsInfo(FD, "function", Ctx);
    for( unsigned int i=0; i<FD->getNumParams(); i++ ) {
        const ParmVarDecl* arg = FD->getParamDecl(i);
        checkBoundsInfo(arg, "arg" + std::to_string(i), Ctx);
    }
#endif

#if USE_PROGRAM_STATE
    const ParmVarDecl* arg0 = FD->getParamDecl(0);
    const MemRegion* arg0region = state->getRegion(arg0, LCtx);
    Loc argLoc = svalBuilder.makeLoc(arg0region);
    SVal argSVal = state->getSVal(argLoc);

    llvm::errs() << "checkBegin: memreg.kind: " << arg0region->getKind() << "\n";

    const CountBoundsExpr* CBE = dyn_cast<CountBoundsExpr>(arg0->getBoundsExpr());
    SVal argBoundSVal = C.getSVal(CBE->getCountExpr());

    SymbolRef from = argSVal.getAsSymbolicExpression();
    SymbolRef to = argBoundSVal.getAsSymbolicExpression();
    //BoundsState to = BoundsState::mkOneBoundsState();

#if DEBUG_DUMP
    llvm::errs() << "\nargsval: ";
    argSVal.dump();
    llvm::errs() << "\nargboundsval: ";
    argBoundSVal.dump();

    SVal bounds2 = state->getSVal(CBE, LCtx);
    llvm::errs() << "\nargboundsval.v2: ";
    bounds2.dump();
#endif

    state = state->set<BoundsMap>(from, to);
    C.addTransition(state);
#endif
}

void ento::registerSimpleBoundsChecker(CheckerManager &mgr) {
  mgr.registerChecker<SimpleBoundsChecker>();
}
