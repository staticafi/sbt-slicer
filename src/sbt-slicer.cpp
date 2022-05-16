#include <set>
#include <string>

#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#ifndef HAVE_LLVM
#error "This code needs LLVM enabled"
#endif

#include <llvm/Config/llvm-config.h>

#if (LLVM_VERSION_MAJOR < 3)
#error "Unsupported version of LLVM"
#endif

#include <dg/tools/llvm-slicer-opts.h>
#include <dg/tools/llvm-slicer-utils.h>
#include <dg/tools/llvm-slicer.h>

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

#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/PrettyStackTrace.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_os_ostream.h>

#if (__clang__)
#pragma clang diagnostic pop // ignore -Wunused-parameter
#else
#pragma GCC diagnostic pop
#endif

#include <fstream>
#include <iostream>

#include "dg/ADT/Queue.h"
#include "dg/llvm/LLVMDG2Dot.h"
#include "dg/llvm/LLVMDGAssemblyAnnotationWriter.h"

#include "git-version.h"

using namespace dg;

using llvm::errs;

using AnnotationOptsT =
        dg::debug::LLVMDGAssemblyAnnotationWriter::AnnotationOptsT;

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
                "(dd: data dependencies, cd:control dependencies,\n"
                "rd: reaching definitions, pta: points-to information,\n"
                "slice: comment out what is going to be sliced away, etc.)\n"
                "for more options, use comma separated list"),
        llvm::cl::value_desc("val1,val2,..."), llvm::cl::init(""),
        llvm::cl::cat(SlicingOpts));

llvm::cl::opt<bool> criteria_are_next_instr(
        "criteria-are-next-instr",
        llvm::cl::desc(
                "Assume that slicing criteria are not the call-sites\n"
                "of the given function, but the instructions that\n"
                "follow the call. I.e. the call is used just to mark\n"
                "the instruction.\n"
                "E.g. for 'crit' being set as the criterion, slicing critera "
                "are all instructions that follow any call of 'crit'.\n"),
        llvm::cl::init(false), llvm::cl::cat(SlicingOpts));

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

    for (const Function &F : *M) {
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

static bool checkThreads(dg::LLVMDependenceGraph &dg) {
    std::set<LLVMNode *> cs;
    return dg.getCallSites("pthread_create", &cs);
}

static bool checkUnsupported(dg::LLVMDependenceGraph & /* dg */) {
    std::set<LLVMNode *> cs;
    bool ret = LLVMDependenceGraph::getCallSites(
            {"pthread_create", "fesetround"}, &cs);
    llvm::errs() << "Unsupported:\n";
    for (auto *c : cs) {
        llvm::errs() << "  " << *(c->getValue()) << "\n";
    }

    return ret;
}

std::unique_ptr<llvm::Module> parseModule(llvm::LLVMContext &context,
                                          const SlicerOptions &options) {
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
void setupStackTraceOnError(int argc, char *argv[]) {
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

int main(int argc, char *argv[]) {
    setupStackTraceOnError(argc, argv);

#if ((LLVM_VERSION_MAJOR >= 6))
    llvm::cl::SetVersionPrinter(
            [](llvm::raw_ostream &) { printf("%s\n", GIT_VERSION); });
#else
    llvm::cl::SetVersionPrinter([]() { printf("%s\n", GIT_VERSION); });
#endif

    SlicerOptions options = parseSlicerOptions(argc, argv);

    if (!options.legacySecondarySlicingCriteria.empty())
        options.legacySecondarySlicingCriteria += ",";

    // we do not want to slice away any assumptions
    // about the code
    // XXX: do this optional only for TEST/SV-COMP?
    options.legacySecondarySlicingCriteria += "__VERIFIER_assume,klee_assume";

    if (memsafety) {
        criteria_are_next_instr = true;
        options.legacySecondarySlicingCriteria += ","
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
                                 criteria_nodes, criteria_are_next_instr)) {
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
