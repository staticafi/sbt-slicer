#include <set>
#include <string>

#include <cassert>
#include <cstdlib>
#include <cstdio>
#include <cstring>

#ifndef HAVE_LLVM
#error "This code needs LLVM enabled"
#endif

#include <llvm/Config/llvm-config.h>

#if (LLVM_VERSION_MAJOR < 3)
#error "Unsupported version of LLVM"
#endif

// ignore unused parameters in LLVM libraries
#if (__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR < 5))
 #include <llvm/Assembly/AssemblyAnnotationWriter.h>
 #include <llvm/Analysis/Verifier.h>
#else // >= 3.5
 #include <llvm/IR/AssemblyAnnotationWriter.h>
 #include <llvm/IR/Verifier.h>
#endif

#if LLVM_VERSION_MAJOR >= 4
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>
#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_os_ostream.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/PrettyStackTrace.h>
#include <llvm/Support/CommandLine.h>

#if (__clang__)
#pragma clang diagnostic pop // ignore -Wunused-parameter
#else
#pragma GCC diagnostic pop
#endif

#include <iostream>
#include <fstream>

#include "llvm/LLVMDependenceGraph.h"
#include "llvm/Slicer.h"
#include "llvm/LLVMDG2Dot.h"
#include "TimeMeasure.h"

#include "llvm/analysis/DefUse.h"
#include "llvm/analysis/PointsTo/PointsTo.h"
#include "analysis/ReachingDefinitions/SemisparseRda.h"
#include "llvm/analysis/ReachingDefinitions/ReachingDefinitions.h"

#include "analysis/PointsTo/PointsToFlowInsensitive.h"
#include "analysis/PointsTo/PointsToFlowSensitive.h"
#include "analysis/PointsTo/PointsToWithInvalidate.h"
#include "analysis/PointsTo/Pointer.h"

#include "git-version.h"

using namespace dg;
using llvm::errs;

enum PtaType {
    fs, fi, inv
};

enum RdaType {
    dense, ss
};

llvm::cl::OptionCategory SlicingOpts("Slicer options", "");

llvm::cl::opt<std::string> output("o",
    llvm::cl::desc("Save the output to given file. If not specified,\n"
                   "a .sliced suffix is used with the original module name."),
    llvm::cl::value_desc("filename"), llvm::cl::init(""), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<std::string> llvmfile(llvm::cl::Positional, llvm::cl::Required,
    llvm::cl::desc("<input file>"), llvm::cl::init(""), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<std::string> slicing_criterion("c", llvm::cl::Required,
    llvm::cl::desc("Slice with respect to the call-sites of a given function\n"
                   "i. e.: '-c foo' or '-c __assert_fail'. Special value is a 'ret'\n"
                   "in which case the slice is taken with respect to the return value\n"
                   "of the main() function. You can use comma separated list of more\n"
                   "function calls, e.g. -c foo,bar\n"), llvm::cl::value_desc("func"),
                   llvm::cl::init(""), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<uint64_t> pta_field_sensitivie("pta-field-sensitive",
    llvm::cl::desc("Make PTA field sensitive/insensitive. The offset in a pointer\n"
                   "is cropped to Offset::UNKNOWNwhen it is greater than N bytes.\n"
                   "Default is full field-sensitivity (N = Offset::UNKNOWN).\n"),
                   llvm::cl::value_desc("N"), llvm::cl::init(Offset::UNKNOWN),
                   llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> rd_strong_update_unknown("rd-strong-update-unknown",
    llvm::cl::desc("Let reaching defintions analysis do strong updates on memory defined\n"
                   "with uknown offset in the case, that new definition overwrites\n"
                   "the whole memory. May be unsound for out-of-bound access\n"),
                   llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> undefined_are_pure("undefined-are-pure",
    llvm::cl::desc("Assume that undefined functions have no side-effects\n"),
                   llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> criteria_are_mem_uses("criteria-are-mem-uses",
    llvm::cl::desc("Assume that slicing criteria are not call-sites, but "
                   "instructions that write/read to/from memory "
                   "using the arguments in the criteria calls. "
                   "E.g. for 'crit' being set as the criterion, slicing critera "
                   "are all load/store that use some 'x' as pointer operand "
                   "for which crit(x) appears in the code\n"),
                   llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<PtaType> pta("pta",
    llvm::cl::desc("Choose pointer analysis to use:"),
    llvm::cl::values(
        clEnumVal(fi, "Flow-insensitive PTA (default)"),
        clEnumVal(fs, "Flow-sensitive PTA"),
        clEnumVal(inv, "PTA with invalidate nodes")
#if LLVM_VERSION_MAJOR < 4
        , nullptr
#endif
        ),
    llvm::cl::init(fi), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<RdaType> rda("rda",
    llvm::cl::desc("Choose reaching definitions analysis to use:"),
    llvm::cl::values(
        clEnumVal(dense, "Dense RDA (default)"),
        clEnumVal(ss, "Semi-sparse RDA")
#if LLVM_VERSION_MAJOR < 4
        , nullptr
#endif
        ),
    llvm::cl::init(dense), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<CD_ALG> CdAlgorithm("cd-alg",
    llvm::cl::desc("Choose control dependencies algorithm to use:"),
    llvm::cl::values(
        clEnumValN(CD_ALG::CLASSIC , "classic", "Ferrante's algorithm (default)"),
        clEnumValN(CD_ALG::CONTROL_EXPRESSION, "ce", "Control expression based (experimental)")
#if LLVM_VERSION_MAJOR < 4
        , nullptr
#endif
         ),
    llvm::cl::init(CD_ALG::CLASSIC), llvm::cl::cat(SlicingOpts));

static bool createEmptyMain(llvm::Module *M)
{
    llvm::Function *main_func = M->getFunction("main");
    if (!main_func) {
        errs() << "No main function found in module. This seems like bug since\n"
                  "here we should have the graph build from main\n";
        return false;
    }

    // delete old function body
    main_func->deleteBody();

    // create new function body that just returns
    llvm::LLVMContext& ctx = M->getContext();
    llvm::BasicBlock* blk = llvm::BasicBlock::Create(ctx, "entry", main_func);
    llvm::Type *Ty = main_func->getReturnType();
    llvm::Value *retval = nullptr;
    if (Ty->isIntegerTy())
        retval = llvm::ConstantInt::get(Ty, 0);
    llvm::ReturnInst::Create(ctx, retval, blk);

    return true;
}

static std::vector<std::string> splitList(const std::string& opt)
{
    std::vector<std::string> ret;
    if (opt.empty())
        return ret;

    size_t old_pos = 0;
    size_t pos = 0;
    while (true) {
        old_pos = pos;

        pos = opt.find(',', pos);
        ret.push_back(opt.substr(old_pos, pos - old_pos));

        if (pos == std::string::npos)
            break;
        else
            ++pos;
    }

    return ret;
}

/// --------------------------------------------------------------------
//   - Slicer class -
//
//  The main class that represents slicer and covers the elementary
//  functionality
/// --------------------------------------------------------------------
class Slicer {
    uint32_t slice_id = 0;
    bool got_slicing_criterion = true;
protected:
    llvm::Module *M;
    std::unique_ptr<LLVMPointerAnalysis> PTA;
    std::unique_ptr<LLVMReachingDefinitions> RD;
    std::set<LLVMNode *> criteria;
    LLVMDependenceGraph dg;
    LLVMSlicer slicer;

    virtual void computeEdges()
    {
        debug::TimeMeasure tm;
        assert(PTA && "BUG: No PTA");
        assert(RD && "BUG: No RD");

        tm.start();
        if (rda == dense) {
            RD->run<dg::analysis::rd::ReachingDefinitionsAnalysis>();
        } else if (rda == ss) {
            RD->run<dg::analysis::rd::SemisparseRda>();
        } else {
            assert( false && "unknown RDA type" );
        }

        tm.stop();
        tm.report("INFO: Reaching defs analysis took");

        LLVMDefUseAnalysis DUA(&dg, RD.get(),
                               PTA.get(), undefined_are_pure);
        tm.start();
        DUA.run(); // add def-use edges according that
        tm.stop();
        tm.report("INFO: Adding Def-Use edges took");

        tm.start();
        // add post-dominator frontiers
        dg.computeControlDependencies(CdAlgorithm);
        tm.stop();
        tm.report("INFO: Computing control dependencies took");
    }

    std::set<LLVMNode *> _getMemoryOperations(const std::set<LLVMNode *>& callsites) {
        std::set<LLVMNode *> nodes;

        for (LLVMNode *cs: callsites) {
            for (unsigned i = 0, e = cs->getOperandsNum(); i < e; ++i) {
                LLVMNode *operand = cs->getOperand(i);
                if (!operand) {
                    continue;
                }

                // now find all store/loads that use this operand
                // as pointer operand. NOTE: strip pointer casts,
                // as instrumentation casts the pointer to *i8
                llvm::Value *llvmOp = operand->getValue()->stripPointerCasts();
                assert(llvmOp && "No llvm value in operand");

                for (auto I = llvmOp->use_begin(), E = llvmOp->use_end(); I != E; ++I) {
#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR < 5))
                    llvm::Value *use = *I;
#else
                    llvm::Value *use = I->getUser();
#endif
                    bool match = false;
                    if (llvm::StoreInst *SI = llvm::dyn_cast<llvm::StoreInst>(use)) {
                        match = (llvmOp == SI->getPointerOperand());
                    } else if (llvm::LoadInst *LI = llvm::dyn_cast<llvm::LoadInst>(use)) {
                        match = (llvmOp == LI->getPointerOperand());
                    }

                    if (match) {
                        LLVMDependenceGraph *local_dg = operand->getDG();
                        LLVMNode *useNode = local_dg->getNode(use);
                        assert(useNode && "DG does not have such node");
                        assert((useNode->getKey() == use) && "wrong node");

                        nodes.insert(useNode);
                    }
                }
            }
        }

        return nodes;
    }

public:
    Slicer(llvm::Module *mod)
    :M(mod),
     PTA(new LLVMPointerAnalysis(mod, pta_field_sensitivie)),
      RD(new LLVMReachingDefinitions(mod, PTA.get(),
                                     rd_strong_update_unknown, undefined_are_pure)) {
        assert(mod && "Need module");
    }

    const std::set<LLVMNode *>& getSlicingCriteria() const { return criteria; }

    const LLVMDependenceGraph& getDG() const { return dg; }
    LLVMDependenceGraph& getDG() { return dg; }

    // shared by old and new analyses
    bool mark()
    {
        debug::TimeMeasure tm;
        std::set<LLVMNode *> callsites;

        std::vector<std::string> criterions = splitList(slicing_criterion);
        assert(!criterions.empty() && "Do not have the slicing criterion");

        // if user wants to slice with respect to the retrn of main
        for (const auto& c : criterions)
            if (c == "ret")
                callsites.insert(dg.getExit());

        // check for slicing criterion here, because
        // we might have built new subgraphs that contain
        // it during points-to analysis
        bool ret = dg.getCallSites(criterions, &callsites);
        got_slicing_criterion = true;
        if (!ret) {
            errs() << "Did not find slicing criterion: "
                   << slicing_criterion << "\n";
            got_slicing_criterion = false;
        }

        // don't go through the graph when we know the result:
        // only empty main will stay there. Just delete the body
        // of main and keep the return value
        if (!got_slicing_criterion)
            return createEmptyMain(M);

        computeEdges();

        // we also do not want to remove any assumptions
        // about the code
        // FIXME: make it configurable and add control dependencies
        // for these functions, so that we slice away the
        // unneeded one
        const char *sc[] = {
            "__VERIFIER_assume",
            "__VERIFIER_exit",
            "klee_assume",
            NULL // termination
        };

        dg.getCallSites(sc, &callsites);

        // do not slice __VERIFIER_assume at all
        // FIXME: do this optional
        slicer.keepFunctionUntouched("__VERIFIER_assume");
        slicer.keepFunctionUntouched("__VERIFIER_exit");
        slice_id = 0xdead;

        if (criteria_are_mem_uses) {
            // instead of nodes for call-sites,
            // get nodes for instructions that use
            // some of the arguments of the calls
            // FIXME: finish me
            auto nodes = _getMemoryOperations(callsites);
            callsites.swap(nodes);

            // we also need to get the calls of "free" function
            // as it uses the memory. Get it again
            // also if we got it already, because
            // _getMemoryOperations removed it.
            dg.getCallSites({"free"}, &callsites);
        }

        tm.start();
        for (LLVMNode *start : criteria)
            slice_id = slicer.mark(start, slice_id);

        tm.stop();
        tm.report("INFO: Finding dependent nodes took");

        return true;
    }

    bool slice()
    {
        // we created an empty main in this case
        if (!got_slicing_criterion)
            return true;

        if (slice_id == 0) {
            if (!mark())
                return false;
        }

        debug::TimeMeasure tm;

        tm.start();
        slicer.slice(&dg, nullptr, slice_id);

        tm.stop();
        tm.report("INFO: Slicing dependence graph took");

        analysis::SlicerStatistics& st = slicer.getStatistics();
        errs() << "INFO: Sliced away " << st.nodesRemoved
               << " from " << st.nodesTotal << " nodes in DG\n";

        return true;
    }

    virtual bool buildDG()
    {
        debug::TimeMeasure tm;

        tm.start();

        if (pta == PtaType::fs)
            PTA->run<analysis::pta::PointsToFlowSensitive>();
        else if (pta == PtaType::fi)
            PTA->run<analysis::pta::PointsToFlowInsensitive>();
        else if (pta == PtaType::inv)
            PTA->run<analysis::pta::PointsToWithInvalidate>();
        else
            assert(0 && "Wrong pointer analysis");

        tm.stop();
        tm.report("INFO: Points-to analysis took");

        dg.build(&*M, PTA.get());

        // verify if the graph is built correctly
        // FIXME - do it optionally (command line argument)
        if (!dg.verify()) {
            errs() << "ERR: verifying failed\n";
            return false;
        }

        return true;
    }
};

static void print_statistics(llvm::Module *M, const char *prefix = nullptr)
{
    using namespace llvm;
    uint64_t inum, bnum, fnum, gnum;
    inum = bnum = fnum = gnum = 0;

    for (auto I = M->begin(), E = M->end(); I != E; ++I) {
        // don't count in declarations
        if (I->size() == 0)
            continue;

        ++fnum;

        for (const BasicBlock& B : *I) {
            ++bnum;
            inum += B.size();
        }
    }

    for (auto I = M->global_begin(), E = M->global_end(); I != E; ++I)
        ++gnum;

    if (prefix)
        errs() << prefix;

    errs() << "Globals/Functions/Blocks/Instr.: "
           << gnum << " " << fnum << " " << bnum << " " << inum << "\n";
}

static bool array_match(llvm::StringRef name, const char *names[])
{
    unsigned idx = 0;
    while(names[idx]) {
        if (name.equals(names[idx]))
            return true;
        ++idx;
    }

    return false;
}

static bool remove_unused_from_module(llvm::Module *M)
{
    using namespace llvm;
    // do not slice away these functions no matter what
    // FIXME do it a vector and fill it dynamically according
    // to what is the setup (like for sv-comp or general..)
    const char *keep[] = {"main", "klee_assume", NULL};

    // when erasing while iterating the slicer crashes
    // so set the to be erased values into container
    // and then erase them
    std::set<Function *> funs;
    std::set<GlobalVariable *> globals;
    std::set<GlobalAlias *> aliases;

    for (auto I = M->begin(), E = M->end(); I != E; ++I) {
        Function *func = &*I;
        if (array_match(func->getName(), keep))
            continue;

        // if the function is unused or we haven't constructed it
        // at all in dependence graph, we can remove it
        // (it may have some uses though - like when one
        // unused func calls the other unused func
        if (func->hasNUses(0))
            funs.insert(func);
    }

    for (auto I = M->global_begin(), E = M->global_end(); I != E; ++I) {
        GlobalVariable *gv = &*I;
        if (gv->hasNUses(0))
            globals.insert(gv);
    }

    for (GlobalAlias& ga : M->getAliasList()) {
        if (ga.hasNUses(0))
            aliases.insert(&ga);
    }

    for (Function *f : funs)
        f->eraseFromParent();
    for (GlobalVariable *gv : globals)
        gv->eraseFromParent();
    for (GlobalAlias *ga : aliases)
        ga->eraseFromParent();

    return (!funs.empty() || !globals.empty() || !aliases.empty());
}

static void remove_unused_from_module_rec(llvm::Module *M)
{
    bool fixpoint;

    do {
        fixpoint = remove_unused_from_module(M);
    } while (fixpoint);
}

// after we slice the LLVM, we somethimes have troubles
// with function declarations:
//
//   Global is external, but doesn't have external or dllimport or weak linkage!
//   i32 (%struct.usbnet*)* @always_connected
//   invalid linkage type for function declaration
//
// This function makes the declarations external
static void make_declarations_external(llvm::Module *M)
{
    using namespace llvm;

    // iterate over all functions in module
    for (auto I = M->begin(), E = M->end(); I != E; ++I) {
        Function *func = &*I;
        if (func->size() == 0) {
            // this will make sure that the linkage has right type
            func->deleteBody();
        }
    }
}

static bool verify_module(llvm::Module *M)
{
    // the verifyModule function returns false if there
    // are no errors

#if ((LLVM_VERSION_MAJOR >= 4) || (LLVM_VERSION_MINOR >= 5))
    return !llvm::verifyModule(*M, &llvm::errs());
#else
    return !llvm::verifyModule(*M, llvm::PrintMessageAction);
#endif
}

static void replace_suffix(std::string& fl, const std::string& with)
{
    if (fl.size() > 2) {
        if (fl.compare(fl.size() - 2, 2, ".o") == 0)
            fl.replace(fl.end() - 2, fl.end(), with);
        else if (fl.compare(fl.size() - 3, 3, ".bc") == 0)
            fl.replace(fl.end() - 3, fl.end(), with);
        else
            fl += with;
    } else {
        fl += with;
    }
}
static bool write_module(llvm::Module *M)
{
    // compose name if not given
    std::string fl;
    if (!output.empty()) {
        fl = output;
    } else {
        fl = llvmfile;
        replace_suffix(fl, ".sliced");
    }

    // open stream to write to
    std::ofstream ofs(fl);
    llvm::raw_os_ostream ostream(ofs);

    // write the module
    errs() << "INFO: saving sliced module to: " << fl.c_str() << "\n";
    llvm::WriteBitcodeToFile(M, ostream);

    return true;
}

static int verify_and_write_module(llvm::Module *M)
{
    if (!verify_module(M)) {
        errs() << "ERR: Verifying module failed, the IR is not valid\n";
        errs() << "INFO: Saving anyway so that you can check it\n";
        return 1;
    }

    if (!write_module(M)) {
        errs() << "Saving sliced module failed\n";
        return 1;
    }

    // exit code
    return 0;
}

static int save_module(llvm::Module *M,
                       bool should_verify_module = true)
{
    if (should_verify_module)
        return verify_and_write_module(M);
    else
        return write_module(M);
}

static void dump_dg_to_dot(LLVMDependenceGraph& dg, bool bb_only = false,
                           uint32_t dump_opts = debug::PRINT_DD | debug::PRINT_CD,
                           const char *suffix = nullptr,
                           const std::set<LLVMNode *>* crit = nullptr)
{
    // compose new name
    std::string fl(llvmfile);
    if (suffix)
        replace_suffix(fl, suffix);
    else
        replace_suffix(fl, ".dot");

    errs() << "INFO: Dumping DG to to " << fl << "\n";

    if (bb_only) {
        debug::LLVMDGDumpBlocks dumper(&dg, dump_opts, fl.c_str());
        dumper.dump();
    } else {
        debug::LLVMDG2Dot dumper(&dg, dump_opts, fl.c_str());
        if (crit)
            dumper.setSlicingCriteria(*crit);
        dumper.dump();
    }
}

int main(int argc, char *argv[])
{
#if LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR < 9
    llvm::sys::PrintStackTraceOnErrorSignal();
#else
    llvm::sys::PrintStackTraceOnErrorSignal(llvm::StringRef());
#endif
    llvm::PrettyStackTraceProgram X(argc, argv);

    llvm::Module *M = nullptr;
    llvm::LLVMContext context;
    llvm::SMDiagnostic SMD;

    llvm::cl::opt<bool> should_verify_module("dont-verify",
        llvm::cl::desc("Verify sliced module (default=true)."),
        llvm::cl::init(true), llvm::cl::cat(SlicingOpts));

    llvm::cl::opt<bool> remove_unused_only("remove-unused-only",
        llvm::cl::desc("Only remove unused parts of module (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

    llvm::cl::opt<bool> statistics("statistics",
        llvm::cl::desc("Print statistics about slicing (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

    llvm::cl::opt<bool> dump_dg("dump-dg",
        llvm::cl::desc("Dump dependence graph to dot (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

    llvm::cl::opt<bool> dump_dg_only("dump-dg-only",
        llvm::cl::desc("Only dump dependence graph to dot,"
                       " do not slice the module (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

    llvm::cl::opt<bool> bb_only("dump-bb-only",
        llvm::cl::desc("Only dump basic blocks of dependence graph to dot"
                       " (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

    // hide all options except ours options
    // this method is available since LLVM 3.7
#if ((LLVM_VERSION_MAJOR > 3)\
      || ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR >= 7)))
    llvm::cl::HideUnrelatedOptions(SlicingOpts);
#endif
    llvm::cl::SetVersionPrinter([](){ printf("%s\n", GIT_VERSION); });
    llvm::cl::ParseCommandLineOptions(argc, argv);

    uint32_t dump_opts = debug::PRINT_CFG | debug::PRINT_DD | debug::PRINT_CD;
    // dump_dg_only implies dumg_dg
    if (dump_dg_only)
        dump_dg = true;

#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR <= 5))
    M = llvm::ParseIRFile(llvmfile, SMD, context);
#else
    auto _M = llvm::parseIRFile(llvmfile, SMD, context);
    // _M is unique pointer, we need to get Module *
    M = _M.get();
#endif

    if (!M) {
        llvm::errs() << "Failed parsing '" << llvmfile << "' file:\n";
        SMD.print(argv[0], errs());
        return 1;
    }

    if (statistics)
        print_statistics(M, "Statistics before ");

    // remove unused from module, we don't need that
    remove_unused_from_module_rec(M);

    if (remove_unused_only) {
        errs() << "INFO: removed unused parts of module, exiting...\n";
        if (statistics)
            print_statistics(M, "Statistics after ");

        return save_module(M, should_verify_module);
    }

    /// ---------------
    // slice the code
    /// ---------------
    Slicer slicer(M);

    // build the dependence graph, so that we can dump it if desired
    if (!slicer.buildDG()) {
        errs() << "ERROR: Failed building DG\n";
        return 1;
    }

    // mark nodes that are going to be in the slice
    slicer.mark();

    if (dump_dg) {
        dump_dg_to_dot(slicer.getDG(), bb_only, dump_opts,
                       nullptr, &slicer.getSlicingCriteria());

        if (dump_dg_only)
            return 0;
    }

    // slice the graph
    if (!slicer.slice()) {
        errs() << "ERROR: Slicing failed\n";
        return 1;
    }

    if (dump_dg) {
        dump_dg_to_dot(slicer.getDG(), bb_only,
                       dump_opts, ".sliced.dot",
                       &slicer.getSlicingCriteria());
    }

    // remove unused from module again, since slicing
    // could and probably did make some other parts unused
    remove_unused_from_module_rec(M);

    // fix linkage of declared functions (if needs to be fixed)
    make_declarations_external(M);

    if (statistics)
        print_statistics(M, "Statistics after ");

    return save_module(M, should_verify_module);
}
