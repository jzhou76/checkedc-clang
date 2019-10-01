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

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"

#include <string>


#define DEBUG_DUMP false
#define BOUNDS_CHECK_WITH_Z3 true
#define TEST_PROGRAM_STATE false
#define USE_PROGRAM_STATE false

using namespace clang;
using namespace ento;

class SymExprGenVisitor : public RecursiveASTVisitor<SymExprGenVisitor> {
    public:
        explicit SymExprGenVisitor(ASTContext *Context)
            : Context(Context) {}

        bool VisitVarDecl(VarDecl *Declaration) {
            return true;
        }

    private:
        ASTContext *Context;
};

class SymExprGenConsumer : public ASTConsumer {
    public:
        explicit SymExprGenConsumer(ASTContext *Context)
            : Visitor(Context) {}

        virtual void HandleTranslationUnit(ASTContext &Context) {
            Visitor.TraverseDecl(Context.getTranslationUnitDecl());
        }
    private:
        SymExprGenVisitor Visitor;
};



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
    SymbolManager& symMgr = svalBuilder.getSymbolManager();
    ASTContext &Ctx = svalBuilder.getContext();
    

    state->getEnvironment().print(llvm::errs(), "\nCheckLocation:: ", "\n", Ctx);

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
//    ASTConsumer * symGen = std::unique_ptr<ASTConsumer>(new SymGenExprConsumer(Ctx));


    const LocationContext *LCtx = C.getLocationContext();
    const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(LCtx->getDecl());
    if (!FD) {
        llvm::errs() << "FD in checkLoc is NULL!\n";
        return;
    }
    FD = FD->getCanonicalDecl();

    SymbolRef symBE;

    const ParmVarDecl* arg0 = FD->getParamDecl(0);
    const Expr* BE = arg0->getBoundsExpr();
    if ( BE ) BE->dumpColor(); else {llvm::errs() << "BoundsExpr of first arg is NULL!\n";}
    SVal BESymVal = state->getSVal(BE, LCtx); // <-- This is the normal way one should read the symbolic values associated with expression in the 'environment'
    SymbolRef BER = BESymVal.getAsSymbol();

    const ParmVarDecl* arg1 = FD->getParamDecl(1);
    //SVal arg1SVal = state->getSVal(state->getLValue(arg1, LCtx));
    SVal arg1SVal = state->getSVal(state->getRegion(arg1, LCtx), arg1->getType());

    if (!BER) {
        llvm::errs() << "BER is NULL (BoundsExpr SymbolRef is not in the ENV)!\n"; // <-- This means that this expression is not processed by the symbolic engine

    /** DEBUG (Symbol conjuring)
     * This is how we can conjure a symbol to encapsulate any given expression (But not knowing anything about the expression itself)
     * **/
    #define CONJUR_SYMBOL false
    #if CONJUR_SYMBOL
        llvm::errs() << "Try a conjured symbol:\n";
//        const SymbolConjured* SC = svalBuilder.conjureSymbol(BE, LCtx, 0);  // <- This triggers an assertion as the expr type is either void or null?!
        const SymbolConjured* SC = symMgr.conjureSymbol(dyn_cast<Stmt>(BE), LCtx, Ctx.IntTy, 0);
        if (!SC) {
            llvm::errs() << "Conjured symbol is also NULL!\n";
            return;
        }
        const SymExpr* parSE = dyn_cast<SymExpr>(SC);
        if (!parSE) {
            llvm::errs() << "Cast failed!\n";
            return;
        }
        symBE = parSE;
    #endif // CONJUR_SYMBOL

        symBE = arg1SVal.getAsSymbol();
    }
    else {
        symBE = BER;
    }
    
    symBE->dump(); llvm::errs() << "\n";
    //return;



    /** DEBUG (BoundsExpr manipulation)
     *  Here we try to get the children info of the expression, and maybe the ParmVar inside the expression by dynamic casting
     */
    #define BOUNDSEXPR_MANIP false
    #if BOUNDSEXPR_MANIP
    const CountBoundsExpr* CBE = dyn_cast<CountBoundsExpr>(arg->getBoundsExpr());
    CBE->dumpColor();
    llvm::errs() << "CBE children:\n";
    for( auto I = CBE->child_begin(); I != CBE->child_end(); I++ ) {
        const Stmt* E = *I;
        if (!E) E->dumpColor(); else llvm::errs() << "--";
        llvm::errs() << "\n";
    }

    const Expr* E = arg->getBoundsExpr();
    llvm::errs() << "After ignoring imp cast:\n";
    if (!E) {E->dumpColor();} else {llvm::errs() << "returned pointer is NULL!\n";}

    SVal argBoundSVal = C.getSVal(CBE->getCountExpr());
    argBoundSVal.dump(); llvm::errs() << "\n";
    //BoundsSym = argBoundSVal.getAsSymbolicExpression();

    /* DEBUG START */
    /* These are debug codes, attempting to get to the ParmVar inside the CountBoundsExpr */
    const DeclRefExpr* t = dyn_cast<DeclRefExpr>(arg->getBoundsExpr());
    if (!t) {llvm::errs() << "t is NULL!\n"; }
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
    #endif // BOUNDSEXPR_MANIP
#endif // !USE_PROGRAM_STATE


    // 3. Encode the expression as a SMT formula
    //    it should be of the form: (idx < lower_bound) v (idx > upper_bound)
    //
    // TODO: currently only expressions of count(n) is handled, generalize for bounds(LB, UB)
    //
    // SMT expression of the bounds expression
    SMTExprRef smtBE = SMTConv::getExpr(solver, Ctx, symBE); //smtBE->print(llvm::errs()); llvm::errs()<<"\n";
    // SMT expression of the index
    SMTExprRef smtIdx = SMTConv::getExpr(solver, Ctx, Idx.getAsSymbol()); //smtIdx->print(llvm::errs()); llvm::errs()<<"\n";
    // SMT expression for (idx > UpperBound)
    SMTExprRef overUB = solver->mkBVUgt(smtIdx, smtBE); //overUB->print(llvm::errs()); llvm::errs()<<"\n";
    // SMT expression for (idx < LowerBound)
    SMTExprRef underLB = solver->mkBVUlt(smtIdx, solver->mkBitvector(llvm::APSInt(32), 32)); //underLB->print(llvm::errs()); llvm::errs()<<"\n";
    
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
    state->getEnvironment().print(llvm::errs(), "checkBegin::\n", "\n", Ctx);


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
