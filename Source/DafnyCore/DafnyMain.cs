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
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging.Abstractions;

namespace Microsoft.Dafny {

  public class DafnyMain {
    public static readonly Dictionary<string, Uri> StandardLibrariesDooUriTarget = new();
    public static readonly Uri StandardLibrariesDooUri = DafnyFile.ExposeInternalUri("DafnyStandardLibraries.dfy",
      new("dllresource://DafnyPipeline/DafnyStandardLibraries.doo"));

    static DafnyMain() {
      foreach (var target in new[] { "cs", "java", "go", "py", "js", "notarget" }) {
        StandardLibrariesDooUriTarget[target] = DafnyFile.ExposeInternalUri($"DafnyStandardLibraries-{target}.dfy",
          new($"dllresource://DafnyPipeline/DafnyStandardLibraries-{target}.doo"));
      }
    }

    public static void MaybePrintProgram(Program program, string filename, bool afterResolver) {
      if (filename == null) {
        return;
      }

      var tw = filename == "-" ? program.Options.OutputWriter : new StreamWriter(filename);
      var pr = new Printer(tw, program.Options, program.Options.PrintMode);
      pr.PrintProgramLargeStack(program, afterResolver);
      if (filename != "-") {
        tw.Dispose();
      }
    }

    /// <summary>
    /// Returns null on success, or an error string otherwise.
    /// </summary>
    public static async Task<(Program Program, string Error)> ParseCheck(TextReader stdIn,
        IReadOnlyList<DafnyFile /*!*/> /*!*/ files, string /*!*/ programName,
        DafnyOptions options)
    //modifies Bpl.options.XmlSink.*;
    {
      var (program, err) = await Parse(files, programName, options);
      if (err != null) {
        return (program, err);
      }

      return (program, Resolve(program));
    }

    public static async Task<(Program Program, string Error)> Parse(IReadOnlyList<DafnyFile> files,
      string programName, DafnyOptions options) {
      Contract.Requires(programName != null);
      Contract.Requires(files != null);

      ErrorReporter reporter = options.DiagnosticsFormat switch {
        DafnyOptions.DiagnosticsFormats.PlainText => new ConsoleErrorReporter(options),
        DafnyOptions.DiagnosticsFormats.JSON => new JsonConsoleErrorReporter(options),
        _ => throw new ArgumentOutOfRangeException()
      };

      var parseResult = await new ProgramParser(NullLogger<ProgramParser>.Instance, OnDiskFileSystem.Instance).
        ParseFiles(programName, files, reporter, CancellationToken.None);
      var program = parseResult.Program;
      var errorCount = program.Reporter.ErrorCount;
      if (errorCount != 0) {
        return (program, $"{errorCount} parse errors detected in {program.Name}");
      }
      return (program, null);
    }

    public static readonly TaskScheduler LargeThreadScheduler =
      CustomStackSizePoolTaskScheduler.Create(0x10000000, Environment.ProcessorCount);

    public static readonly TaskFactory LargeStackFactory = new(CancellationToken.None,
      TaskCreationOptions.DenyChildAttach, TaskContinuationOptions.None, LargeThreadScheduler);

    public static string Resolve(Program program) {
      if (program.Options.NoResolve || program.Options.NoTypecheck) {
        return null;
      }

      var programResolver = new ProgramResolver(program);
#pragma warning disable VSTHRD002
      LargeStackFactory.StartNew(() => programResolver.Resolve(CancellationToken.None)).Wait();
#pragma warning restore VSTHRD002
      MaybePrintProgram(program, program.Options.DafnyPrintResolvedFile, true);

      var errorCount = program.Reporter.CountExceptVerifierAndCompiler(ErrorLevel.Error);
      if (errorCount != 0) {
        return $"{errorCount} resolution/type errors detected in {program.Name}";
      }

      return null; // success
    }

    public static async Task<(PipelineOutcome Outcome, PipelineStatistics Statistics)> BoogieOnce(
      ErrorReporter errorReporter, DafnyOptions options,
      TextWriter output,
      ExecutionEngine engine,
      string baseFile,
      string moduleName,
      Boogie.Program boogieProgram, string programId) {
      var moduleId = (programId ?? "main_program_id") + "_" + moduleName;

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
  }
}
