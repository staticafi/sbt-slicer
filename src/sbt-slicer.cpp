#include <cassert>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>

#include <dg/tools/llvm-slicer-opts.h>
#include <dg/tools/llvm-slicer-preprocess.h>
#include <dg/tools/llvm-slicer-utils.h>
#include <dg/tools/llvm-slicer.h>
#include "git-version.h"

#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/raw_ostream.h>

#include <dg/ADT/Queue.h>
#include <dg/util/debug.h>

using namespace dg;

using dg::LLVMDataDependenceAnalysisOptions;
using dg::LLVMPointerAnalysisOptions;
using llvm::errs;

using AnnotationOptsT =
        dg::debug::LLVMDGAssemblyAnnotationWriter::AnnotationOptsT;

llvm::cl::opt<bool> enable_debug(
        "dbg", llvm::cl::desc("Enable debugging messages (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> should_verify_module(
        "dont-verify", llvm::cl::desc("Verify sliced module (default=true)."),
        llvm::cl::init(true), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> abort_on_threads(
        "abort-on-threads",
        llvm::cl::desc("Abort when threads are present (default=true)."),
        llvm::cl::init(true), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool>
        abort_on_unsupp("abort-on-unsupported",
                        llvm::cl::desc("Abort when some unsupported feature is "
                                       "present (default=true)."),
                        llvm::cl::init(true), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> remove_unused_only(
        "remove-unused-only",
        llvm::cl::desc("Only remove unused parts of module (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> statistics(
        "statistics",
        llvm::cl::desc("Print statistics about slicing (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool>
        dump_dg("dump-dg",
                llvm::cl::desc("Dump dependence graph to dot (default=false)."),
                llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> dump_dg_only(
        "dump-dg-only",
        llvm::cl::desc("Only dump dependence graph to dot,"
                       " do not slice the module (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> dump_bb_only(
        "dump-bb-only",
        llvm::cl::desc("Only dump basic blocks of dependence graph to dot"
                       " (default=false)."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

llvm::cl::opt<std::string> annotationOpts(
        "annotate",
        llvm::cl::desc(
                "Save annotated version of module as a text (.ll).\n"
                "Options:\n"
                "  dd: data dependencies,\n"
                "  cd:control dependencies,\n"
                "  pta: points-to information,\n"
                "  memacc: memory accesses of instructions,\n"
                "  slice: comment out what is going to be sliced away).\n"
                "for more options, use comma separated list"),
        llvm::cl::value_desc("val1,val2,..."), llvm::cl::init(""),
        llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> memsafety(
        "memsafety",
        llvm::cl::desc(
                "Assume that slicing criteria are potentially memory-unsafe "
                "instructions. This option implies criteria-are-next-instr, "
                "i.e., the slicing criteria are \"only marked\" "
                "by the given slicing criteria."),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

// mapping of AllocaInst to the names of C variables
std::map<const llvm::Value *, std::string> valuesToVariables;

static void maybe_print_statistics(llvm::Module *M,
                                   const char *prefix = nullptr) {
    if (!statistics)
        return;

    using namespace llvm;
    uint64_t inum, bnum, fnum, gnum;
    inum = bnum = fnum = gnum = 0;

    for (const auto &F : *M) {
        // don't count in declarations
        if (F.empty())
            continue;

        ++fnum;

        for (const BasicBlock &B : F) {
            ++bnum;
            inum += B.size();
        }
    }

    for (auto I = M->global_begin(), E = M->global_end(); I != E; ++I)
        ++gnum;

    if (prefix)
        errs() << prefix;

    errs() << "Globals/Functions/Blocks/Instr.: " << gnum << " " << fnum << " "
           << bnum << " " << inum << "\n";
}

static AnnotationOptsT parseAnnotationOptions(const std::string &annot) {
    if (annot.empty())
        return {};

    AnnotationOptsT opts{};
    std::vector<std::string> lst = splitList(annot);
    for (const std::string &opt : lst) {
        if (opt == "dd")
            opts |= AnnotationOptsT::ANNOTATE_DD;
        else if (opt == "cd" || opt == "cda")
            opts |= AnnotationOptsT::ANNOTATE_CD;
        else if (opt == "dda" || opt == "du")
            opts |= AnnotationOptsT::ANNOTATE_DEF;
        else if (opt == "pta")
            opts |= AnnotationOptsT::ANNOTATE_PTR;
        else if (opt == "memacc")
            opts |= AnnotationOptsT::ANNOTATE_MEMORYACC;
        else if (opt == "slice" || opt == "sl" || opt == "slicer")
            opts |= AnnotationOptsT::ANNOTATE_SLICE;
    }

    return opts;
}

static bool checkThreads(dg::LLVMDependenceGraph &dg) {
    std::set<LLVMNode *> cs;
    return dg.getCallSites("pthread_create", &cs);
}

static bool checkUnsupported(dg::LLVMDependenceGraph & /* dg */) {
    std::set<LLVMNode *> cs;
    bool ret = LLVMDependenceGraph::getCallSites(
            {"pthread_create", "fesetround"}, &cs);
    bool ret = dg.getCallSites(
	{"pthread_create", "fesetround","longjmp"}, &cs);
    llvm::errs() << "Unsupported:\n";
    for (auto *c : cs) {
        llvm::errs() << "  " << *(c->getValue()) << "\n";
    }

    return ret;
}

int main(int argc, char *argv[]) {
    setupStackTraceOnError(argc, argv);

#if ((LLVM_VERSION_MAJOR >= 6))
    llvm::cl::SetVersionPrinter([](llvm::raw_ostream & /*unused*/) {
        printf("%s\n", GIT_VERSION);
    });
#else
    llvm::cl::SetVersionPrinter([]() { printf("%s\n", GIT_VERSION); });
#endif

    SlicerOptions options = parseSlicerOptions(argc, argv,
                                               /* requireCrit = */ true);

    if (enable_debug) {
        DBG_ENABLE();
    }

    if (!options.legacySecondarySlicingCriteria.empty())
        options.legacySecondarySlicingCriteria += ",";

    // we do not want to slice away any assumptions
    // about the code
    // XXX: do this optional only for TEST/SV-COMP?
    options.legacySecondarySlicingCriteria += "__VERIFIER_assume,klee_assume";

    if (memsafety) {
        options.criteriaAreNextInstr = true;
        options.legacySecondarySlicingCriteria += ","
                                                  "llvm.lifetime.start.p0i8(),"
                                                  "llvm.lifetime.end.p0i8(),"
                                                  "__VERIFIER_scope_enter(),"
                                                  "__VERIFIER_scope_leave(),"
                                                  "free()";
    }

    // dump_dg_only implies dumg_dg
    if (dump_dg_only) {
        dump_dg = true;
    }

    llvm::LLVMContext context;
    std::unique_ptr<llvm::Module> M =
            parseModule("sbt-slicer", context, options);
    if (!M)
        return 1;

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
        errs() << "[sbt-slicer] removed unused parts of module, exiting...\n";
        maybe_print_statistics(M.get(), "Statistics after ");
        return writer.saveModule(should_verify_module);
    }

    /// ---------------
    // slice the code
    /// ---------------
    if (options.cutoffDiverging && options.dgOptions.threads) {
        llvm::errs() << "[sbt-slicer] threads are enabled, not cutting off "
                        "diverging\n";
        options.cutoffDiverging = false;
    }

    if (options.cutoffDiverging) {
        DBG(sbt - slicer, "Searching for slicing criteria values");
        auto csvalues = getSlicingCriteriaValues(
                *M, options.slicingCriteria, options.legacySlicingCriteria,
                options.legacySecondarySlicingCriteria,
                options.criteriaAreNextInstr);
        if (csvalues.empty()) {
            llvm::errs() << "No reachable slicing criteria: '"
                         << options.slicingCriteria << "' '"
                         << options.legacySlicingCriteria << "'\n";
            ::Slicer slicer(M.get(), options);
            if (!slicer.createEmptyMain()) {
                llvm::errs() << "ERROR: failed creating an empty main\n";
                return 1;
            }

            maybe_print_statistics(M.get(), "Statistics after ");
            return writer.cleanAndSaveModule(should_verify_module);
        }

        DBG(sbt - slicer, "Cutting off diverging branches");
        if (!llvmdg::cutoffDivergingBranches(
                    *M, options.dgOptions.entryFunction, csvalues)) {
            errs() << "[sbt-slicer]: Failed cutting off diverging branches\n";
            return 1;
        }

        maybe_print_statistics(M.get(), "Statistics after cutoff-diverging ");
    }

    ::Slicer slicer(M.get(), options);
    if (!slicer.buildDG()) {
        errs() << "ERROR: Failed building DG\n";
        return 1;
    }

    ModuleAnnotator annotator(options, &slicer.getDG(),
                              parseAnnotationOptions(annotationOpts));

    if (abort_on_unsupp) {
        if (checkUnsupported(slicer.getDG())) {
            llvm::errs() << "ERROR: Found unsupported feature, giving up\n";
            return 1;
        }
    } else if (abort_on_threads && checkThreads(slicer.getDG())) {
        // threads are now unsupported, so have the check in 'else if'
        llvm::errs() << "ERROR: Found threads, giving up\n";
        return 1;
    }

    std::set<LLVMNode *> criteria_nodes;
    if (!getSlicingCriteriaNodes(slicer.getDG(), options.slicingCriteria,
                                 options.legacySlicingCriteria,
                                 options.legacySecondarySlicingCriteria,
                                 criteria_nodes,
                                 options.criteriaAreNextInstr)) {
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
                     << options.slicingCriteria << "' '"
                     << options.legacySlicingCriteria << "'\n";
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
