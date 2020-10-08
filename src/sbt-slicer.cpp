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

#include "dg/tools/llvm-slicer.h"
#include "dg/tools/llvm-slicer-opts.h"
#include "dg/tools/llvm-slicer-utils.h"

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
#include "dg/llvm/LLVMDGAssemblyAnnotationWriter.h"

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

#if 0
bool findSecondarySlicingCriteria(std::set<LLVMNode *>& criteria_nodes,
                                  const std::set<std::string>& secondaryControlCriteria,
                                  const std::set<std::string>& secondaryDataCriteria);




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
#if LLVM_VERSION_MAJOR >= 8
        const Value *calledValue = callInst->getCalledOperand();
#else
        const Value *calledValue = callInst->getCalledValue();
#endif
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
    } else if (slicer.getOptions().dgOptions.CDAOptions.isNonterminationSensitive()) {
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
    if (slicer.getOptions().dgOptions.CDAOptions.isNonterminationSensitive()) {
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
#endif

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

    std::set<LLVMNode *> criteria_nodes;
    if (!getSlicingCriteriaNodes(slicer.getDG(),
                                 options.slicingCriteria,
                                 options.secondarySlicingCriteria,
                                 criteria_nodes,
                                 criteria_are_next_instr)) {
        llvm::errs() << "ERROR: Failed finding slicing criteria: '"
                     << options.slicingCriteria << "'\n";

        if (annotator.shouldAnnotate()) {
            slicer.computeDependencies();
            annotator.annotate();
        }

        return 1;
    }

    if (criteria_nodes.empty()) {
        llvm::errs() << "No reachable slicing criteria: '"
                     << options.slicingCriteria << "'\n";
        if (annotator.shouldAnnotate()) {
            slicer.computeDependencies();
            annotator.annotate();
        }

        if (!slicer.createEmptyMain()) {
            llvm::errs() << "ERROR: failed creating an empty main\n";
            return 1;
        }

        maybe_print_statistics(M.get(), "Statistics after ");
        return writer.cleanAndSaveModule(should_verify_module);
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
