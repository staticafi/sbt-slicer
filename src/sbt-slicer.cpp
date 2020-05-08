#include <set>
#include <string>

#include <cassert>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cctype>

#ifndef HAVE_LLVM
#error "This code needs LLVM enabled"
#endif

#include <llvm/Config/llvm-config.h>

#if (LLVM_VERSION_MAJOR < 3)
#error "Unsupported version of LLVM"
#endif

#include "llvm-slicer.h"
#include "llvm-slicer-opts.h"
#include "llvm-slicer-utils.h"

// ignore unused parameters in LLVM libraries
#if (__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

#if LLVM_VERSION_MAJOR >= 4
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>
#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_os_ostream.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/PrettyStackTrace.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/IntrinsicInst.h>

#if (__clang__)
#pragma clang diagnostic pop // ignore -Wunused-parameter
#else
#pragma GCC diagnostic pop
#endif

#include <iostream>
#include <fstream>

#include "dg/ADT/Queue.h"
#include "dg/llvm/LLVMDG2Dot.h"
#include "LLVMDGAssemblyAnnotationWriter.h"
#include "llvm-utils.h"

using namespace dg;

using llvm::errs;
using dg::LLVMPointerAnalysisOptions;
using dg::LLVMDataDependenceAnalysisOptions;

using AnnotationOptsT
    = dg::debug::LLVMDGAssemblyAnnotationWriter::AnnotationOptsT;


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

llvm::cl::opt<bool> dump_bb_only("dump-bb-only",
    llvm::cl::desc("Only dump basic blocks of dependence graph to dot"
                   " (default=false)."),
    llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<std::string> annotationOpts("annotate",
    llvm::cl::desc("Save annotated version of module as a text (.ll).\n"
                   "(dd: data dependencies, cd:control dependencies,\n"
                   "rd: reaching definitions, pta: points-to information,\n"
                   "slice: comment out what is going to be sliced away, etc.)\n"
                   "for more options, use comma separated list"),
    llvm::cl::value_desc("val1,val2,..."), llvm::cl::init(""),
    llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> criteria_are_next_instr("criteria-are-next-instr",
    llvm::cl::desc("Assume that slicing criteria are not the call-sites\n"
                   "of the given function, but the instructions that\n"
                   "follow the call. I.e. the call is used just to mark\n"
                   "the instruction.\n"
                   "E.g. for 'crit' being set as the criterion, slicing critera "
                   "are all instructions that follow any call of 'crit'.\n"),
                   llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> memsafety("memsafety",
    llvm::cl::desc("Assume that slicing criteria are potentially memory-unsafe "
                   "instructions. This option implies criteria-are-next-instr, "
                   "i.e., the slicing criteria are \"only marked\" "
                   "by the given slicing criteria."),
                   llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

// mapping of AllocaInst to the names of C variables
std::map<const llvm::Value *, std::string> valuesToVariables;

class ModuleWriter {
    const SlicerOptions& options;
    llvm::Module *M;

public:
    ModuleWriter(const SlicerOptions& o,
                 llvm::Module *m)
    : options(o), M(m) {}

    int cleanAndSaveModule(bool should_verify_module = true) {
        // remove unneeded parts of the module
        removeUnusedFromModule();

        // fix linkage of declared functions (if needs to be fixed)
        makeDeclarationsExternal();

        return saveModule(should_verify_module);
    }

    int saveModule(bool should_verify_module = true)
    {
        if (should_verify_module)
            return verifyAndWriteModule();
        else
            return writeModule();
    }

    void removeUnusedFromModule()
    {
        bool fixpoint;

        do {
            fixpoint = _removeUnusedFromModule();
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
    void makeDeclarationsExternal()
    {
        using namespace llvm;

        // iterate over all functions in module
        for (auto& F : *M) {
            if (F.size() == 0) {
                // this will make sure that the linkage has right type
                F.deleteBody();
            }
        }
    }

private:
    bool writeModule() {
        // compose name if not given
        std::string fl;
        if (!options.outputFile.empty()) {
            fl = options.outputFile;
        } else {
            fl = options.inputFile;
            replace_suffix(fl, ".sliced");
        }

        // open stream to write to
        std::ofstream ofs(fl);
        llvm::raw_os_ostream ostream(ofs);

        // write the module
        errs() << "INFO: saving sliced module to: " << fl.c_str() << "\n";

    #if (LLVM_VERSION_MAJOR > 6)
        llvm::WriteBitcodeToFile(*M, ostream);
    #else
        llvm::WriteBitcodeToFile(M, ostream);
    #endif

        return true;
    }

    bool verifyModule()
    {
        // the verifyModule function returns false if there
        // are no errors

#if ((LLVM_VERSION_MAJOR >= 4) || (LLVM_VERSION_MINOR >= 5))
        return !llvm::verifyModule(*M, &llvm::errs());
#else
       return !llvm::verifyModule(*M, llvm::PrintMessageAction);
#endif
    }


    int verifyAndWriteModule()
    {
        if (!verifyModule()) {
            errs() << "ERR: Verifying module failed, the IR is not valid\n";
            errs() << "INFO: Saving anyway so that you can check it\n";
            return 1;
        }

        if (!writeModule()) {
            errs() << "Saving sliced module failed\n";
            return 1;
        }

        // exit code
        return 0;
    }

    bool _removeUnusedFromModule()
    {
        using namespace llvm;
        // do not slice away these functions no matter what
        // FIXME do it a vector and fill it dynamically according
        // to what is the setup (like for sv-comp or general..)
        const char *keep[] = {options.dgOptions.entryFunction.c_str(),
                              nullptr};

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

};

static void maybe_print_statistics(llvm::Module *M, const char *prefix = nullptr)
{
    if (!statistics)
        return;

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

class DGDumper {
    const SlicerOptions& options;
    LLVMDependenceGraph *dg;
    bool bb_only{false};
    uint32_t dump_opts{debug::PRINT_DD | debug::PRINT_CD | debug::PRINT_USE | debug::PRINT_ID};

public:
    DGDumper(const SlicerOptions& opts,
             LLVMDependenceGraph *dg,
             bool bb_only = false,
             uint32_t dump_opts = debug::PRINT_DD | debug::PRINT_CD | debug::PRINT_USE | debug::PRINT_ID)
    : options(opts), dg(dg), bb_only(bb_only), dump_opts(dump_opts) {}

    void dumpToDot(const char *suffix = nullptr) {
        // compose new name
        std::string fl(options.inputFile);
        if (suffix)
            replace_suffix(fl, suffix);
        else
            replace_suffix(fl, ".dot");

        errs() << "INFO: Dumping DG to to " << fl << "\n";

        if (bb_only) {
            debug::LLVMDGDumpBlocks dumper(dg, dump_opts, fl.c_str());
            dumper.dump();
        } else {
            debug::LLVMDG2Dot dumper(dg, dump_opts, fl.c_str());
            dumper.dump();
        }
    }
};

class ModuleAnnotator {
    const SlicerOptions& options;
    LLVMDependenceGraph *dg;
    AnnotationOptsT annotationOptions;

public:
    ModuleAnnotator(const SlicerOptions& o,
                    LLVMDependenceGraph *dg,
                    AnnotationOptsT annotO)
    : options(o), dg(dg), annotationOptions(annotO) {}

    bool shouldAnnotate() const { return annotationOptions != 0; }

    void annotate(const std::set<LLVMNode *> *criteria = nullptr)
    {
        // compose name
        std::string fl(options.inputFile);
        fl.replace(fl.end() - 3, fl.end(), "-debug.ll");

        // open stream to write to
        std::ofstream ofs(fl);
        llvm::raw_os_ostream outputstream(ofs);

        std::string module_comment =
        "; -- Generated by llvm-slicer --\n"
        ";   * slicing criteria: '" + options.slicingCriteria + "'\n" +
        ";   * secondary slicing criteria: '" + options.secondarySlicingCriteria + "'\n" +
        ";   * forward slice: '" + std::to_string(options.forwardSlicing) + "'\n" +
        ";   * remove slicing criteria: '"
             + std::to_string(options.removeSlicingCriteria) + "'\n" +
        ";   * undefined are pure: '"
             + std::to_string(options.dgOptions.DDAOptions.undefinedArePure) + "'\n" +
        ";   * pointer analysis: ";
        if (options.dgOptions.PTAOptions.analysisType
                == LLVMPointerAnalysisOptions::AnalysisType::fi)
            module_comment += "flow-insensitive\n";
        else if (options.dgOptions.PTAOptions.analysisType
                    == LLVMPointerAnalysisOptions::AnalysisType::fs)
            module_comment += "flow-sensitive\n";
        else if (options.dgOptions.PTAOptions.analysisType
                    == LLVMPointerAnalysisOptions::AnalysisType::inv)
            module_comment += "flow-sensitive with invalidate\n";

        module_comment+= ";   * PTA field sensitivity: ";
        if (options.dgOptions.PTAOptions.fieldSensitivity == Offset::UNKNOWN)
            module_comment += "full\n\n";
        else
            module_comment
                += std::to_string(*options.dgOptions.PTAOptions.fieldSensitivity)
                   + "\n\n";

        errs() << "INFO: Saving IR with annotations to " << fl << "\n";
        auto annot
            = new dg::debug::LLVMDGAssemblyAnnotationWriter(annotationOptions,
                                                            dg->getPTA(),
                                                            dg->getDDA(),
                                                            criteria);
        annot->emitModuleComment(std::move(module_comment));
        llvm::Module *M = dg->getModule();
        M->print(outputstream, annot);

        delete annot;
    }
};


static bool usesTheVariable(LLVMDependenceGraph& dg,
                            const llvm::Value *v,
                            const std::string& var)
{
    auto pts = dg.getPTA()->getLLVMPointsTo(v);
    if (pts.hasUnknown())
        return true; // it may be a definition of the variable, we do not know

    for (const auto& ptr : pts) {
        auto name = valuesToVariables.find(ptr.value);
        if (name != valuesToVariables.end()) {
            if (name->second == var)
                return true;
        }
    }

    return false;
}

template <typename InstT>
static bool useOfTheVar(LLVMDependenceGraph& dg,
                        const llvm::Instruction& I,
                        const std::string& var)
{
    // check that we store to that variable
    const InstT *tmp = llvm::dyn_cast<InstT>(&I);
    if (!tmp)
        return false;

    return usesTheVariable(dg, tmp->getPointerOperand(), var);
}

static bool isStoreToTheVar(LLVMDependenceGraph& dg,
                            const llvm::Instruction& I,
                            const std::string& var)
{
    return useOfTheVar<llvm::StoreInst>(dg, I, var);
}

static bool isLoadOfTheVar(LLVMDependenceGraph& dg,
                           const llvm::Instruction& I,
                           const std::string& var)
{
    return useOfTheVar<llvm::LoadInst>(dg, I, var);
}


static bool instMatchesCrit(LLVMDependenceGraph& dg,
                            const llvm::Instruction& I,
                            const std::vector<std::pair<int, std::string>>& parsedCrit)
{
    for (const auto& c : parsedCrit) {
        auto& Loc = I.getDebugLoc();
#if (LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR < 7)
        if (Loc.getLine() <= 0) {
#else
        if (!Loc) {
#endif
            continue;
        }

        if (static_cast<int>(Loc.getLine()) != c.first)
            continue;

        if (isStoreToTheVar(dg, I, c.second) ||
            isLoadOfTheVar(dg, I, c.second)) {
            llvm::errs() << "Matched line " << c.first << " with variable "
                         << c.second << " to:\n" << I << "\n";
            return true;
        }
    }

    return false;
}

static bool globalMatchesCrit(const llvm::GlobalVariable& G,
                              const std::vector<std::pair<int, std::string>>& parsedCrit)
{
    for (const auto& c : parsedCrit) {
        if (c.first != -1)
            continue;
        if (c.second == G.getName().str()) {
            llvm::errs() << "Matched global variable "
                         << c.second << " to:\n" << G << "\n";
            return true;
        }
    }

    return false;
}

static inline bool isNumber(const std::string& s) {
    assert(!s.empty());

    for (const auto c : s)
        if (!isdigit(c))
            return false;

    return true;
}

static void getLineCriteriaNodes(LLVMDependenceGraph& dg,
                                 std::vector<std::string>& criteria,
                                 std::set<LLVMNode *>& nodes)
{
    assert(!criteria.empty() && "No criteria given");

    std::vector<std::pair<int, std::string>> parsedCrit;
    for (auto& crit : criteria) {
        auto parts = splitList(crit, ':');
        assert(parts.size() == 2);

        // parse the line number
        if (parts[0].empty()) {
            // global variable
            parsedCrit.emplace_back(-1, parts[1]);
        } else if (isNumber(parts[0])) {
            int line = atoi(parts[0].c_str());
            if (line > 0)
                parsedCrit.emplace_back(line, parts[1]);
        } else {
            llvm::errs() << "Invalid line: '" << parts[0] << "'. "
                         << "Needs to be a number or empty for global variables.\n";
        }
    }

    assert(!parsedCrit.empty() && "Failed parsing criteria");

#if (LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR < 7)
    llvm::errs() << "WARNING: Variables names matching is not supported for LLVM older than 3.7\n";
    llvm::errs() << "WARNING: The slicing criteria with variables names will not work\n";
#else
    // create the mapping from LLVM values to C variable names
    for (auto& it : getConstructedFunctions()) {
        for (auto& I : llvm::instructions(*llvm::cast<llvm::Function>(it.first))) {
            if (const llvm::DbgDeclareInst *DD = llvm::dyn_cast<llvm::DbgDeclareInst>(&I)) {
                auto val = DD->getAddress();
                valuesToVariables[val] = DD->getVariable()->getName().str();
            } else if (const llvm::DbgValueInst *DV
                        = llvm::dyn_cast<llvm::DbgValueInst>(&I)) {
                auto val = DV->getValue();
                valuesToVariables[val] = DV->getVariable()->getName().str();
            }
        }
    }

    bool no_dbg = valuesToVariables.empty();
    if (no_dbg) {
        llvm::errs() << "No debugging information found in program,\n"
                     << "slicing criteria with lines and variables will work\n"
                     << "only for global variables.\n"
                     << "You can still use the criteria based on call sites ;)\n";
    }

    for (const auto& GV : dg.getModule()->globals()) {
        valuesToVariables[&GV] = GV.getName().str();
    }

    // try match globals
    for (auto& G : dg.getModule()->globals()) {
        if (globalMatchesCrit(G, parsedCrit)) {
            LLVMNode *nd = dg.getGlobalNode(&G);
            assert(nd);
            nodes.insert(nd);
        }
    }

    // we do not have any mapping, we will not match anything
    if (no_dbg) {
        return;
    }

    // map line criteria to nodes
    for (auto& it : getConstructedFunctions()) {
        for (auto& I : llvm::instructions(*llvm::cast<llvm::Function>(it.first))) {
            if (instMatchesCrit(dg, I, parsedCrit)) {
                LLVMNode *nd = it.second->getNode(&I);
                assert(nd);
                nodes.insert(nd);
            }
        }
    }
#endif // LLVM > 3.6
}

/*
static void
addDependenciesForWrites(llvm::Instruction *succ,
                         LLVMDependenceGraph& dg,
                         std::set<LLVMNode *>& nodes) {

    const llvm::Module *M = dg.getModule();
    LLVMPointerAnalysis *PTA = dg.getPTA();
    LLVMDataDependenceAnalysis *DDA = dg.getDDA();

    // FIXME: do this only for marker configuration
    // FIXME: what about memcpy/memset/... ??
    if (!llvm::isa<llvm::StoreInst>(succ))
        return;

    // if the successor is Store, we want to take also the memory it
    // writes to as slicing criteria (its reaching definitions, more
    // precisely).
    auto pts = PTA->getLLVMPointsTo(succ->getOperand(1));
    if (pts.hasUnknown()) {
        llvm::errs() << "WARNING: Store to unknown memory as "
                        "slicing criterion (unknown memory ignored)\n";
        llvm::errs() << *succ << "\n";
    }
    for (const auto& ptr : pts) {
        auto size = dg::analysis::getAllocatedSize(succ->getOperand(0)->getType(),
                                                   &M->getDataLayout());
        auto defs = DDA->getLLVMDefinitions(succ, ptr.value, ptr.offset, size);
        const auto& funs = getConstructedFunctions();
        if (defs.empty()) {
            llvm::errs() << "WARNING: got no definitions for " << *ptr.value << "\n";
            llvm::errs() << "WARNING: at " << *succ << "\n";
        }
        for (auto val : defs) {
            auto I = llvm::dyn_cast<llvm::Instruction>(val);
            if (!I) {
                auto G = llvm::dyn_cast<llvm::GlobalValue>(val);
                assert(G && "Whata!");
                auto GN = dg.getGlobalNode(G);
                assert(GN && "Do not have global node");
                nodes.insert(GN);
                continue;
            }
            auto it = funs.find(const_cast<llvm::Function *>(I->getParent()->getParent()));
            assert(it != funs.end());
            auto local_dg = it->second;
            assert(local_dg);

            LLVMNode *node = local_dg->getNode(val);
            assert(node && "DG does not have such node");
            nodes.insert(node);
        }
    }
}
*/

std::set<LLVMNode *> _mapToNextInstr(LLVMDependenceGraph&,
                                     const std::set<LLVMNode *>& callsites) {
    std::set<LLVMNode *> nodes;

    for (LLVMNode *cs: callsites) {
        llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(cs->getValue());
        assert(I && "Callsite is not an instruction");
        llvm::Instruction *succ = I->getNextNode();
        if (!succ) {
            llvm::errs() << *I << "has no successor that could be criterion\n";
            // abort for now
            abort();
        }

        LLVMDependenceGraph *local_dg = cs->getDG();
        LLVMNode *node = local_dg->getNode(succ);
        assert(node && "DG does not have such node");
        nodes.insert(node);

       // We do that now using the secondar slicing criteria
       //if (memsafety) {
       //    addDependenciesForWrites(succ, dg, nodes);
       //}
    }

    return nodes;
}

static std::set<LLVMNode *> getSlicingCriteriaNodes(::Slicer& slicer,
                                                    const std::string& slicingCriteria)
{
    LLVMDependenceGraph& dg = slicer.getDG();
    std::set<LLVMNode *> nodes;
    std::vector<std::string> criteria = splitList(slicingCriteria);
    assert(!criteria.empty() && "Did not get slicing criteria");

    std::vector<std::string> line_criteria;
    std::vector<std::string> node_criteria;
    std::tie(line_criteria, node_criteria)
        = splitStringVector(criteria, [](std::string& s) -> bool
            { return s.find(':') != std::string::npos; }
          );

    // if user wants to slice with respect to the return of main,
    // insert the ret instructions to the nodes.
    for (const auto& c : node_criteria) {
        if (c == "ret") {
            LLVMNode *exit = dg.getExit();
            // We could insert just the exit node, but this way we will
            // get annotations to the functions.
            for (auto it = exit->rev_control_begin(), et = exit->rev_control_end();
                 it != et; ++it) {
                nodes.insert(*it);
            }
        }
    }

    // map the criteria to nodes
    if (!node_criteria.empty())
        dg.getCallSites(node_criteria, &nodes);
    if (!line_criteria.empty())
        getLineCriteriaNodes(dg, line_criteria, nodes);

    if (criteria_are_next_instr && !nodes.empty()) {
        // if criteria are next instructions for memsafety,
        // we need to have data dependencies computed,
        // because we search for dependencies of
        // instructions that write to memory
        // XXX: we use the secondary slicing criteria now
        //if (memsafety) {
        //    slicer.computeDependencies();
        //}

        // instead of nodes for call-sites,
        // get nodes for instructions that use
        // some of the arguments of the calls
        auto mappedNodes = _mapToNextInstr(dg, nodes);
        nodes.swap(mappedNodes);
    }


    return nodes;
}

static std::pair<std::set<std::string>, std::set<std::string>>
parseSecondarySlicingCriteria(const std::string& slicingCriteria)
{
    std::vector<std::string> criteria = splitList(slicingCriteria);

    std::set<std::string> control_criteria;
    std::set<std::string> data_criteria;

    // if user wants to slice with respect to the return of main,
    // insert the ret instructions to the nodes.
    for (const auto& c : criteria) {
        auto s = c.size();
        if (s > 2 && c[s - 2] == '(' && c[s - 1] == ')')
            data_criteria.insert(c.substr(0, s - 2));
        else
            control_criteria.insert(c);
    }

    return {control_criteria, data_criteria};
}

// FIXME: copied from LLVMDependenceGraph.cpp, do not duplicate the code
static bool isCallTo(LLVMNode *callNode, const std::set<std::string>& names)
{
    using namespace llvm;

    if (!isa<llvm::CallInst>(callNode->getValue())) {
        return false;
    }

    // if the function is undefined, it has no subgraphs,
    // but is not called via function pointer
    if (!callNode->hasSubgraphs()) {
        const CallInst *callInst = cast<CallInst>(callNode->getValue());
        const Value *calledValue = callInst->getCalledValue();
        const Function *func = dyn_cast<Function>(calledValue->stripPointerCasts());
        // in the case we haven't run points-to analysis
        if (!func)
            return false;

        return array_match(func->getName(), names);
    } else {
        // simply iterate over the subgraphs, get the entry node
        // and check it
        for (LLVMDependenceGraph *dg : callNode->getSubgraphs()) {
            LLVMNode *entry = dg->getEntry();
            assert(entry && "No entry node in graph");

            const Function *func
                = cast<Function>(entry->getValue()->stripPointerCasts());
            return array_match(func->getName(), names);
        }
    }

    return false;
}

static inline
void checkSecondarySlicingCrit(::Slicer& slicer,
                               const std::set<LLVMNode *>& criteria_nodes,
                               std::set<LLVMNode *>& result,
                               const std::set<std::string>& secondaryControlCriteria,
                               const std::set<std::string>& secondaryDataCriteria,
                               LLVMNode *nd,
                               const std::set<std::string>& recursiveFuns) {
    if (isCallTo(nd, secondaryControlCriteria)) {
        llvm::errs() << "Found (control) conditional SC: "
                     << *nd->getValue() << "\n";
        result.insert(nd);
    } if (isCallTo(nd, secondaryDataCriteria)) {
        auto *PTA = slicer.getDG().getPTA();
        // check that the used memory overlap
        auto ndmem = PTA->getAccessedMemory(
                            llvm::cast<llvm::Instruction>(nd->getValue()));

        for (auto *crit : criteria_nodes) {
            auto critmem = PTA->getAccessedMemory(
                            llvm::cast<llvm::Instruction>(crit->getValue()));
            if (critmem.first || ndmem.first) {
                llvm::errs() << "Found possible data conditional SC"
                             << " (access of unknown memory): "
                             << *nd->getValue() << "\n";
                result.insert(nd);
                break;
            } else if (ndmem.second.overlaps(critmem.second)) {
                llvm::errs() << "Found data conditional SC: "
                             << *nd->getValue() << "\n";
                result.insert(nd);
                break;
            }
        }
    } else if (slicer.getOptions().dgOptions.cdAlgorithm == dg::CD_ALG::NTSCD) {
        if (isCallTo(nd, recursiveFuns)) {
            llvm::errs() << "Found (ntscd) conditional SC: "
                         << *nd->getValue() << "\n";
            result.insert(nd);
        }
        if (auto param = nd->getParameters()) {
            if (auto noret = param->getNoReturn()) {
                for (auto I = noret->rev_control_begin(),
                          E = noret->rev_control_end();
                          I != E; ++I) {
                    llvm::errs() << "Found (ntscd-noret) conditional SC: "
                                 << *(*I)->getValue() << "\n";
                    result.insert(nd);
                }
            }
        }
    }
}

static std::set<std::string>
getRecursiveFuns(::Slicer& slicer) {
    std::set<std::string> recursiveFuns;

    assert(!slicer.getOptions().dgOptions.PTAOptions.isSVF()
            && "Unsupported PTA");

    auto *PTA = static_cast<DGLLVMPointerAnalysis*>(slicer.getDG().getPTA());
    auto& cg = PTA->getPTA()->getPG()->getCallGraph();
    if (cg.empty())  // no (defined) functions are called
        return recursiveFuns;

    auto *entrynd = PTA->getPointsToNode(slicer.getModule()->getFunction("main"));
    auto *entry = cg.get(entrynd);
    assert(entry && "CallGraph has no node for the main function");

    auto SCCs = dg::SCC<dg::GenericCallGraph<dg::PSNode *>::FuncNode>().compute(entry);
    for (auto& component : SCCs) {
        if (component.size() > 1 ||
            (component.size() == 1 && component[0]->calls(component[0]))) {

            for (auto *funcnd : component) {
                auto *fun = funcnd->getValue()->getUserData<llvm::Function>();
                llvm::errs() << "Recursive fun: " << fun->getName() << "\n";
                recursiveFuns.insert(fun->getName().str());
            }
        }
    }

   return recursiveFuns;
}

// mark nodes that are going to be in the slice
// XXX: we gather not secondary SC that are on a path from
// entry to some criterion but that are on some path to
// some criterion, i.e. if there's unreachable code,
// this may be an overapproximation.
bool findSecondarySlicingCriteria(::Slicer& slicer,
                                  std::set<LLVMNode *>& criteria_nodes,
                                  const std::set<std::string>& secondaryControlCriteria,
                                  const std::set<std::string>& secondaryDataCriteria)
{
    std::set<std::string> recursiveFuns;
    if (slicer.getOptions().dgOptions.cdAlgorithm == dg::CD_ALG::NTSCD) {
        recursiveFuns = getRecursiveFuns(slicer);
    }

    // FIXME: do this more efficiently (and use the new DFS class)
    std::set<LLVMNode *> visited;
    ADT::QueueLIFO<LLVMNode *> queue;
    auto result = criteria_nodes;
    for (auto&c : criteria_nodes) {
        // the criteria may be a global variable and in that case it has no
        // basic block (but also no predecessors, so we can skip it)
        if (!c->getBBlock())
            continue;

        queue.push(c);
        visited.insert(c);
    }

    while (!queue.empty()) {
        auto cur = queue.pop();
        auto bblock = cur->getBBlock();
        assert(bblock && "No BBlock for a node");

        // last block in the function,
        // continue into the called functions
        if (bblock->predecessors().empty()) {
            auto *local_dg = cur->getDG();
            for (auto *caller : local_dg->getCallers()) {
                if (visited.insert(caller).second) {
                    queue.push(caller);
                }
            }
        } else {
            for (auto pred : bblock->predecessors()) {
               auto term = pred->getLastNode();
               if (visited.insert(term).second) {
                    queue.push(term);
               }
            }
        }

        // we search the graph backward, but the blocks forwards
        for (auto nd : bblock->getNodes()) {
            checkSecondarySlicingCrit(slicer, criteria_nodes, result,
                                      secondaryControlCriteria,
                                      secondaryDataCriteria, nd,
                                      recursiveFuns);

            // search interprocedurally
            if (nd->hasSubgraphs()) {
                for (auto dg : nd->getSubgraphs()) {
                    auto exit = dg->getExit();
                    assert(exit && "No exit in a graph");
                    if (visited.insert(exit).second)
                        queue.push(exit);
                }
            }
            // bail out here, so that we do not add instructions that
            // are not on an (interprocedural) path to some criterion
            // (without this check, we could add e.g. nodes
            // that follow some call but that are not on a path
            // to some criterion.
            // This node can also by a CSC, so we must perform this
            // check after call to checkSecondarySlicingCrit
            if (nd == cur)
                break;

            // because of calls and returns we may already visited this node
            if (!visited.insert(nd).second)
                break; // visited this node
        }
    }

    criteria_nodes.swap(result);

    return true;
}


static AnnotationOptsT parseAnnotationOptions(const std::string& annot)
{
    if (annot.empty())
        return {};

    AnnotationOptsT opts{};
    std::vector<std::string> lst = splitList(annot);
    for (const std::string& opt : lst) {
        if (opt == "dd")
            opts |= AnnotationOptsT::ANNOTATE_DD;
        else if (opt == "cd")
            opts |= AnnotationOptsT::ANNOTATE_CD;
        else if (opt == "pta")
            opts |= AnnotationOptsT::ANNOTATE_PTR;
        else if (opt == "memacc")
            opts |= AnnotationOptsT::ANNOTATE_MEMORYACC;
        else if (opt == "slice" || opt == "sl" || opt == "slicer")
            opts |= AnnotationOptsT::ANNOTATE_SLICE;
    }

    return opts;
}

std::unique_ptr<llvm::Module> parseModule(llvm::LLVMContext& context,
                                          const SlicerOptions& options)
{
    llvm::SMDiagnostic SMD;

#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR <= 5))
    auto _M = llvm::ParseIRFile(options.inputFile, SMD, context);
    auto M = std::unique_ptr<llvm::Module>(_M);
#else
    auto M = llvm::parseIRFile(options.inputFile, SMD, context);
    // _M is unique pointer, we need to get Module *
#endif

    if (!M) {
        SMD.print("llvm-slicer", llvm::errs());
    }

    return M;
}

#ifndef USING_SANITIZERS
void setupStackTraceOnError(int argc, char *argv[])
{

#if LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR < 9
    llvm::sys::PrintStackTraceOnErrorSignal();
#else
    llvm::sys::PrintStackTraceOnErrorSignal(llvm::StringRef());
#endif
    llvm::PrettyStackTraceProgram X(argc, argv);

}
#else
void setupStackTraceOnError(int, char **) {}
#endif // not USING_SANITIZERS

int main(int argc, char *argv[])
{
    setupStackTraceOnError(argc, argv);

    SlicerOptions options = parseSlicerOptions(argc, argv);

    if (!options.secondarySlicingCriteria.empty())
        options.secondarySlicingCriteria += ",";

    // we do not want to slice away any assumptions
    // about the code
    // XXX: do this optional only for TEST/SV-COMP?
    options.secondarySlicingCriteria +=
        "__VERIFIER_assume,klee_assume";

    if (memsafety) {
        criteria_are_next_instr = true;
        options.secondarySlicingCriteria += ","
            "llvm.lifetime.start.p0i8(),"
            "llvm.lifetime.end.p0i8(),"
            "__VERIFIER_scope_enter(),"
            "__VERIFIER_scope_leave(),"
            "free()";
    }

    // dump_dg_only implies dumg_dg
    if (dump_dg_only)
        dump_dg = true;

    llvm::LLVMContext context;
    std::unique_ptr<llvm::Module> M = parseModule(context, options);
    if (!M) {
        llvm::errs() << "Failed parsing '" << options.inputFile << "' file:\n";
        return 1;
    }

    if (!M->getFunction(options.dgOptions.entryFunction)) {
        llvm::errs() << "The entry function not found: "
                     << options.dgOptions.entryFunction << "\n";
        return 1;
    }

    maybe_print_statistics(M.get(), "Statistics before ");

    // remove unused from module, we don't need that
    ModuleWriter writer(options, M.get());
    writer.removeUnusedFromModule();

    if (remove_unused_only) {
        errs() << "INFO: removed unused parts of module, exiting...\n";
        maybe_print_statistics(M.get(), "Statistics after ");
        return writer.saveModule(should_verify_module);
    }

    /// ---------------
    // slice the code
    /// ---------------

    ::Slicer slicer(M.get(), options);
    if (!slicer.buildDG()) {
        errs() << "ERROR: Failed building DG\n";
        return 1;
    }

    ModuleAnnotator annotator(options, &slicer.getDG(),
                              parseAnnotationOptions(annotationOpts));

    auto criteria_nodes = getSlicingCriteriaNodes(slicer,
                                                  options.slicingCriteria);
    if (criteria_nodes.empty()) {
        llvm::errs() << "Did not find slicing criteria: '"
                     << options.slicingCriteria << "'\n";
        if (annotator.shouldAnnotate()) {
            slicer.computeDependencies();
            annotator.annotate();
        }

        if (!slicer.createEmptyMain())
            return 1;

        maybe_print_statistics(M.get(), "Statistics after ");
        return writer.cleanAndSaveModule(should_verify_module);
    }

    auto secondaryCriteria
        = parseSecondarySlicingCriteria(options.secondarySlicingCriteria);
    const auto& secondaryControlCriteria = secondaryCriteria.first;
    const auto& secondaryDataCriteria = secondaryCriteria.second;

    // mark nodes that are going to be in the slice
    if (!findSecondarySlicingCriteria(slicer, criteria_nodes,
                                      secondaryControlCriteria,
                                      secondaryDataCriteria)) {
        llvm::errs() << "Finding conditional slicing criteria nodes failed\n";
        return 1;
    }

    if (options.dgOptions.threads) {
        // FIXME: searching for conditional SC does not work for
        // threaded programs, so we must add it as extra SC
        options.additionalSlicingCriteria.push_back("__VERIFIER_assume");
        options.additionalSlicingCriteria.push_back("__VERIFIER_exit");
    }

    // mark nodes that are going to be in the slice
    if (!slicer.mark(criteria_nodes)) {
        llvm::errs() << "Finding dependent nodes failed\n";
        return 1;
    }

    // print debugging llvm IR if user asked for it
    if (annotator.shouldAnnotate())
        annotator.annotate(&criteria_nodes);

    DGDumper dumper(options, &slicer.getDG(), dump_bb_only);
    if (dump_dg) {
        dumper.dumpToDot();

        if (dump_dg_only)
            return 0;
    }

    // slice the graph
    if (!slicer.slice()) {
        errs() << "ERROR: Slicing failed\n";
        return 1;
    }

    if (dump_dg) {
        dumper.dumpToDot(".sliced.dot");
    }

    // remove unused from module again, since slicing
    // could and probably did make some other parts unused
    maybe_print_statistics(M.get(), "Statistics after ");
    return writer.cleanAndSaveModule(should_verify_module);
}
