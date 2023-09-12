//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using DafnyCore;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Microsoft.Dafny.ProofObligationDescription;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;

namespace Microsoft.Dafny {

  public class IllegalDafnyFile : Exception {
    public bool ProcessingError { get; }

    public IllegalDafnyFile(bool processingError = false) {
      this.ProcessingError = processingError;
    }
  }

  public class DafnyMain {

    public static void MaybePrintProgram(Program program, string filename, bool afterResolver) {
      if (filename == null) {
        return;
      }

      var tw = filename == "-" ? program.Options.OutputWriter : new StreamWriter(filename);
      var pr = new Printer(tw, program.Options, program.Options.PrintMode);
      pr.PrintProgramLargeStack(program, afterResolver);
    }

    /// <summary>
    /// Returns null on success, or an error string otherwise.
    /// </summary>
    public static string ParseCheck(TextReader stdIn, IReadOnlyList<DafnyFile /*!*/> /*!*/ files, string /*!*/ programName,
        DafnyOptions options, out Program program)
    //modifies Bpl.options.XmlSink.*;
    {
      string err = Parse(files, programName, options, out program);
      if (err != null) {
        return err;
      }

      return Resolve(program);
    }

    public static string Parse(IReadOnlyList<DafnyFile> files, string programName, DafnyOptions options,
      out Program program) {
      Contract.Requires(programName != null);
      Contract.Requires(files != null);
      program = null;

      ErrorReporter reporter = options.DiagnosticsFormat switch {
        DafnyOptions.DiagnosticsFormats.PlainText => new ConsoleErrorReporter(options),
        DafnyOptions.DiagnosticsFormats.JSON => new JsonConsoleErrorReporter(options),
        _ => throw new ArgumentOutOfRangeException()
      };

      program = new ProgramParser().ParseFiles(programName, files, reporter, CancellationToken.None);
      var errorCount = program.Reporter.ErrorCount;
      if (errorCount != 0) {
        return $"{errorCount} parse errors detected in {program.Name}";
      }
      return null;
    }

    private static readonly TaskScheduler largeThreadScheduler =
      CustomStackSizePoolTaskScheduler.Create(0x10000000, Environment.ProcessorCount);

    public static readonly TaskFactory LargeStackFactory = new(CancellationToken.None,
      TaskCreationOptions.DenyChildAttach, TaskContinuationOptions.None, largeThreadScheduler);

    public static string Resolve(Program program) {
      if (program.Options.NoResolve || program.Options.NoTypecheck) {
        return null;
      }

      var programResolver = new ProgramResolver(program);
      LargeStackFactory.StartNew(() => programResolver.Resolve(CancellationToken.None)).Wait();
      MaybePrintProgram(program, program.Options.DafnyPrintResolvedFile, true);

      if (program.Reporter.ErrorCountUntilResolver != 0) {
        return string.Format("{0} resolution/type errors detected in {1}", program.Reporter.Count(ErrorLevel.Error),
          program.Name);
      }

      return null; // success
    }

    public static async Task<(PipelineOutcome Outcome, PipelineStatistics Statistics)> BoogieOnce(
      DafnyOptions options,
      TextWriter output,
      ExecutionEngine engine,
      string baseFile,
      string moduleName,
      Microsoft.Boogie.Program boogieProgram, string programId) {
      var moduleId = (programId ?? "main_program_id") + "_" + moduleName;
      var z3NotFoundMessage = $@"
Z3 not found. Please either provide a path to the `z3` executable using
the `--solver-path <path>` option, manually place the `z3` directory
next to the `dafny` executable you are using (this directory should
contain `bin/z3-{DafnyOptions.DefaultZ3Version}` or `bin/z3-{DafnyOptions.DefaultZ3Version}.exe`), or set the PATH environment variable
to also include a directory containing the `z3` executable.
";

      var proverPath = options.ProverOptions.Find(o => o.StartsWith("PROVER_PATH="));
      if (proverPath is null && options.Verify) {
        options.OutputWriter.WriteLine(z3NotFoundMessage);
        return (PipelineOutcome.FatalError, new PipelineStatistics());
      }

      string bplFilename;
      if (options.PrintFile != null) {
        bplFilename = options.PrintFile;
      } else {
        string baseName = cce.NonNull(Path.GetFileName(baseFile));
        baseName = cce.NonNull(Path.ChangeExtension(baseName, "bpl"));
        bplFilename = Path.Combine(Path.GetTempPath(), baseName);
      }

      bplFilename = BoogieProgramSuffix(bplFilename, moduleName);
      var (outcome, stats) = await BoogiePipelineWithRerun(options,
        output, engine, boogieProgram, bplFilename,
        1 < options.VerifySnapshots ? moduleId : null);
      return (outcome, stats);
    }

    public static string BoogieProgramSuffix(string printFile, string suffix) {
      var baseName = Path.GetFileNameWithoutExtension(printFile);
      var dirName = Path.GetDirectoryName(printFile);

      return Path.Combine(dirName, baseName + "_" + suffix + Path.GetExtension(printFile));
    }

    public static bool IsBoogieVerified(PipelineOutcome outcome, PipelineStatistics statistics) {
      return (outcome == PipelineOutcome.Done || outcome == PipelineOutcome.VerificationCompleted)
             && statistics.ErrorCount == 0
             && statistics.InconclusiveCount == 0
             && statistics.TimeoutCount == 0
             && statistics.OutOfResourceCount == 0
             && statistics.OutOfMemoryCount == 0;
    }

    /// <summary>
    /// Resolve, type check, infer invariants for, and verify the given Boogie program.
    /// The intention is that this Boogie program has been produced by translation from something
    /// else.  Hence, any resolution errors and type checking errors are due to errors in
    /// the translation.
    /// The method prints errors for resolution and type checking errors, but still returns
    /// their error code.
    /// </summary>
    private static async Task<(PipelineOutcome Outcome, PipelineStatistics Statistics)> BoogiePipelineWithRerun(
      DafnyOptions options,
      TextWriter output, ExecutionEngine engine, Microsoft.Boogie.Program /*!*/ program, string /*!*/ bplFileName,
      string programId) {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);

      var stats = new PipelineStatistics();
      var outcome = engine.ResolveAndTypecheck(program, bplFileName, out _);
      switch (outcome) {
        case PipelineOutcome.Done:
          return (outcome, stats);

        case PipelineOutcome.ResolutionError:
        case PipelineOutcome.TypeCheckingError:
          engine.PrintBplFile(bplFileName, program, false, false, options.PrettyPrint);
          await options.OutputWriter.WriteLineAsync();
          await options.OutputWriter.WriteLineAsync(
            "*** Encountered internal translation error - re-running Boogie to get better debug information");
          await options.OutputWriter.WriteLineAsync();

          var /*!*/
            fileNames = new List<string /*!*/> { bplFileName };
          var reparsedProgram = engine.ParseBoogieProgram(fileNames, true);
          if (reparsedProgram != null) {
            engine.ResolveAndTypecheck(reparsedProgram, bplFileName, out _);
          }

          return (outcome, stats);

        case PipelineOutcome.ResolvedAndTypeChecked:
          engine.EliminateDeadVariables(program);
          engine.CollectModSets(program);
          engine.CoalesceBlocks(program);
          engine.Inline(program);
          var inferAndVerifyOutcome = await engine.InferAndVerify(output, program, stats, programId);
          return (inferAndVerifyOutcome, stats);

        default:
          Contract.Assert(false);
          throw new cce.UnreachableException(); // unexpected outcome
      }
    }

    public static void WarnAboutSuspiciousDependencies(DafnyOptions dafnyOptions, ErrorReporter reporter, ProofDependencyManager depManager) {
      var verificationResults = (dafnyOptions.Printer as DafnyConsolePrinter).VerificationResults.ToList();
      var orderedResults =
        verificationResults.OrderBy(vr =>
          (vr.Item1.tok.filename, vr.Item1.tok.line, vr.Item1.tok.col));
      foreach (var (implementation, result) in orderedResults) {
        WarnAboutSuspiciousDependenciesForImplementation(dafnyOptions, reporter, depManager, implementation, result);
      }
    }

    public static void WarnAboutSuspiciousDependenciesForImplementation(DafnyOptions dafnyOptions, ErrorReporter reporter, ProofDependencyManager depManager, Implementation implementation, VerificationResult result) {
      var potentialDependencies = depManager.GetPotentialDependenciesForDefinition(implementation.VerboseName);
      var usedDependencies =
        result
          .VCResults
          .SelectMany(vcResult => vcResult.coveredElements.Select(depManager.GetFullIdDependency))
          .OrderBy(dep => (dep.RangeString(), dep.Description));
      var unusedDependencies =
        potentialDependencies
          .Except(usedDependencies)
          .OrderBy(dep => (dep.RangeString(), dep.Description));

      var unusedObligations = unusedDependencies.OfType<ProofObligationDependency>();
      var unusedRequires = unusedDependencies.OfType<RequiresDependency>();
      var unusedEnsures = unusedDependencies.OfType<EnsuresDependency>();
      var unusedAssumeStatements =
        unusedDependencies
          .OfType<AssumptionDependency>()
          .Where(d => d.Description.Contains("assume statement"));
      if (dafnyOptions.Get(CommonOptionBag.WarnVacuity)) {
        foreach (var dep in unusedObligations) {
          if (ShouldWarnVacuous(implementation.VerboseName, dep)) {
            reporter.Warning(MessageSource.Verifier, "", dep.Range, $"vacuous proof: {dep.Description}");
          }
        }

        foreach (var dep in unusedEnsures) {
          if (ShouldWarnVacuous(implementation.VerboseName, dep)) {
            reporter.Warning(MessageSource.Verifier, "", dep.Range, $"vacuous proof of ensures clause ({dep.SolverLabel})");
          }
        }
      }

      if (dafnyOptions.Get(CommonOptionBag.WarnRedundantAssumptions)) {
        foreach (var dep in unusedRequires) {
          reporter.Warning(MessageSource.Verifier, "", dep.Range, $"unnecessary requires clause");
        }

        foreach (var dep in unusedAssumeStatements) {
          reporter.Warning(MessageSource.Verifier, "", dep.Range, $"unnecessary assumption");
        }
      }
    }

    /// <summary>
    /// Some proof obligations that don't show up in the dependency list
    /// are innocuous. Either they come about because of internal Dafny
    /// design choices that the programmer has no control over, or they
    /// just aren't meaningful in context. This method identifies cases
    /// where it doesn't make sense to issue a warning. Many of these
    /// cases should perhaps be eliminated by changing the translator
    /// to not generate vacuous proof goals, but that may be a difficult
    /// change to make.
    /// </summary>
    /// <param name="dep">the dependency to examine</param>
    /// <returns>false to skip warning about the absence of this
    /// dependency, true otherwise</returns>
    private static bool ShouldWarnVacuous(string verboseName, ProofDependency dep) {
      if (dep is ProofObligationDependency poDep) {
        // Dafny generates some assertions about definite assignment whose
        // proofs are always vacuous. Since these aren't written by Dafny
        // programmers, it's safe to just skip them all.
        if (poDep.ProofObligation is DefiniteAssignment) {
          return false;
        }

        // Similarly here
        if (poDep.ProofObligation is MatchIsComplete or AlternativeIsComplete) {
          return false;
        }

      }

      // Ensures clauses are often proven vacuously during well-formedness checks.
      if (verboseName.Contains("well-formedness") && dep is EnsuresDependency) {
        return false;
      }

      return true;
    }
  }
}
