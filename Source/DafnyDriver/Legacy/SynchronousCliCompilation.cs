//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// DafnyDriver
//       - main program for taking a Dafny program and verifying it
//---------------------------------------------------------------------------------------------

using System.Collections.Concurrent;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using System.Diagnostics;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;
using VC;

namespace Microsoft.Dafny {

  /// <summary>
  /// Calls into different phases of Dafny's compilation pipeline,
  /// such as parsing, resolution, verification and code generation
  /// 
  /// Will be replaced by CompilationManager
  /// </summary>
  public class SynchronousCliCompilation : IDisposable {
    private readonly ExecutionEngine engine;

    public SynchronousCliCompilation(DafnyOptions dafnyOptions) {
      engine = ExecutionEngine.CreateWithoutSharedCache(dafnyOptions);
    }

    public static async Task<int> Run(DafnyOptions options) {
      options.RunningBoogieFromCommandLine = true;

      var backend = GetBackend(options);
      if (backend == null) {
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      options.Backend = backend;

      var (getFilesExitCode, dafnyFiles, otherFiles) = await GetDafnyFiles(options);
      if (getFilesExitCode != ExitValue.SUCCESS) {
        return (int)getFilesExitCode;
      }

      using var driver = new SynchronousCliCompilation(options);
      ProofDependencyManager depManager = new();
      var exitValue = await driver.ProcessFilesAsync(dafnyFiles, otherFiles.AsReadOnly(), options, depManager);
      if (options.Get(CommonOptionBag.VerificationLogFormat)?.Any() == true) {
        try {
          LegacyVerificationResultLogger.RaiseTestLoggerEvents(options, depManager);
        } catch (ArgumentException ae) {
          await options.OutputWriter.Status($"*** Error: {ae.Message}");
          exitValue = ExitValue.PREPROCESSING_ERROR;
        }
      }

      options.XmlSink?.Close();

      if (options.Wait) {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }

      return (int)exitValue;
    }

    public static async Task<(ExitValue ExitValue,
      List<DafnyFile> DafnyFiles,
      List<string> OtherFiles)> GetDafnyFiles(DafnyOptions options) {
      if (options.Printer is NullPrinter) {
        options.Printer = new DafnyConsolePrinter(options);
      }

      if (options.DafnyProject != null) {
        foreach (var uri in options.DafnyProject.GetRootSourceUris(OnDiskFileSystem.Instance)) {
          options.CliRootSourceUris.Add(uri);
        }
      }

      var dafnyFiles = new List<DafnyFile>();
      var otherFiles = new List<string>();
      var outputWriter = options.OutputWriter;

      var consoleErrorReporter = new ConsoleErrorReporter(options);
      if (options.DafnyProject != null) {
        options.DafnyProject.Errors.CopyDiagnostics(consoleErrorReporter);
        if (options.DafnyProject.Errors.HasErrors) {
          return (ExitValue.PREPROCESSING_ERROR, [], []);
        }
      }

      if (options.UseStdin) {
        var dafnyFile = DafnyFile.HandleStandardInput(options, Token.NoToken);
        dafnyFiles.Add(dafnyFile);
        options.CliRootSourceUris.Add(dafnyFile.Uri);
      } else if (options.CliRootSourceUris.Count == 0) {
        await options.ErrorWriter.WriteLineAsync("*** Error: No input files were specified in command-line. " + options.Environment);
        return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
      }
      if (options.XmlSink != null) {
        string errMsg = options.XmlSink.Open();
        if (errMsg != null) {
          await options.ErrorWriter.WriteLineAsync("*** Error: " + errMsg);
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        }
      }
      if (options.ShowEnv == ExecutionEngineOptions.ShowEnvironment.Always) {
        await outputWriter.Status(options.Environment);
      }

      ISet<String> filesSeen = new HashSet<string>();
      var libraryFiles = CommonOptionBag.SplitOptionValueIntoFiles(options.LibraryFiles).ToHashSet();
      foreach (var file in options.CliRootSourceUris.Where(u => u.IsFile).Select(u => u.LocalPath).
                 Concat(libraryFiles).Distinct()) {
        Contract.Assert(file != null);
        var extension = Path.GetExtension(file);
        if (extension != null) { extension = extension.ToLower(); }

        var relative = Path.GetFileName(file);
        bool useRelative = options.UseBaseNameForFileName || relative.StartsWith("-");
        var nameToShow = useRelative ? relative
          : Path.GetRelativePath(Directory.GetCurrentDirectory(), file);
        var supportedExtensions = options.Backend.SupportedExtensions;
        bool isDafnyFile = false;
        try {
          await foreach (var df in DafnyFile.CreateAndValidate(
                           OnDiskFileSystem.Instance, consoleErrorReporter, options, new Uri(Path.GetFullPath(file)),
                           Token.Cli, options.LibraryFiles.Contains(file))) {
            if (!filesSeen.Add(df.CanonicalPath)) {
              continue; // silently ignore duplicate
            }
            dafnyFiles.Add(df);
            isDafnyFile = true;
          }
          if (consoleErrorReporter.FailCompilation) {
            return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
          }
        } catch (ArgumentException) {
          await options.ErrorWriter.WriteLineAsync($"*** Error: {nameToShow}: ");
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        } catch (Exception e) {
          await options.ErrorWriter.WriteLineAsync($"*** Error: {nameToShow}: {e.Message}");
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        }

        if (supportedExtensions.Contains(extension)) {
          // .h files are not part of the build, they are just emitted as includes
          // TODO: This should be delegated to the backend instead (i.e. the CppCompilerBackend)
          if (File.Exists(file) || extension == ".h") {
            otherFiles.Add(file);
          } else {
            await options.OutputWriter.Status($"*** Error: file {nameToShow} not found");
            return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
          }
        } else if (options.AllowSourceFolders && Directory.Exists(file)) {
          options.SourceFolders.Add(file);
        } else if (!isDafnyFile) {
          string errorOnNotRecognized;
          if (options.UsingNewCli && string.IsNullOrEmpty(extension) && file.Length > 0) {
            errorOnNotRecognized =
              $"*** Error: Command-line argument '{nameToShow}' is neither a recognized option nor a filename with a supported extension ({string.Join(", ", Enumerable.Repeat(".dfy", 1).Concat(supportedExtensions))}).";
          } else if (string.IsNullOrEmpty(extension) && file.Length > 0 && (file[0] == '/' || file[0] == '-')) {
            errorOnNotRecognized =
              $"*** Error: Command-line argument '{nameToShow}' is neither a recognized option nor a filename with a supported extension ({string.Join(", ", Enumerable.Repeat(".dfy", 1).Concat(supportedExtensions))}).";
          } else {
            errorOnNotRecognized =
              $"*** Error: '{nameToShow}': Filename extension '{extension}' is not supported. Input files must be Dafny programs (.dfy) or supported auxiliary files ({string.Join(", ", supportedExtensions)})";
          }

          await options.OutputWriter.Status(errorOnNotRecognized);
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        }
      }

      if (dafnyFiles.Count == 0 && options.SourceFolders.Count == 0) {
        if (!options.AllowSourceFolders) {
          options.Printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files");
          // TODO: With the test on CliRootUris.Count above, this code is no longer reachable
          await options.OutputWriter.Status("*** Error: The command-line contains no .dfy files");
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        }

        options.Printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files or folders");
        //options.Printer.ErrorWriteLine(Console.Out,
        //  "Usage:\ndafny format [--check] [--print] <file/folder> <file/folder>...\nYou can use '.' for the current directory");
        return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
      }

      // Add standard library .doo files after explicitly provided source files,
      // only because if they are added first, one might be used as the program name,
      // which is not handled well.
      if (options.Get(CommonOptionBag.UseStandardLibraries)) {
        if (options.Backend is LibraryBackend) {
          options.Set(CommonOptionBag.TranslateStandardLibrary, false);
        }

        // For now the standard libraries are still translated from scratch.
        // This creates issues with separate compilation and will be addressed in https://github.com/dafny-lang/dafny/pull/4877
        var asLibrary = !options.Get(CommonOptionBag.TranslateStandardLibrary);

        var reporter = new ConsoleErrorReporter(options);
        if (options.CompilerName is null or "cs" or "java" or "go" or "py" or "js") {
          var targetName = options.CompilerName ?? "notarget";
          var stdlibDooUri = DafnyMain.StandardLibrariesDooUriTarget[targetName];
          options.CliRootSourceUris.Add(stdlibDooUri);
          await foreach (var targetSpecificFile in DafnyFile.CreateAndValidate(OnDiskFileSystem.Instance, reporter, options, stdlibDooUri, Token.Cli, asLibrary)) {
            dafnyFiles.Add(targetSpecificFile);
          }
        }

        options.CliRootSourceUris.Add(DafnyMain.StandardLibrariesDooUri);
        await foreach (var targetAgnosticFile in DafnyFile.CreateAndValidate(OnDiskFileSystem.Instance, reporter, options, DafnyMain.StandardLibrariesDooUri, Token.Cli, asLibrary)) {
          dafnyFiles.Add(targetAgnosticFile);
        }
      }

      return (ExitValue.SUCCESS, dafnyFiles, otherFiles);
    }

    private static IExecutableBackend GetBackend(DafnyOptions options) {
      if (options.Backend?.TargetId == options.CompilerName) {
        return options.Backend;
      }

      var backends = options.Plugins.SelectMany(p => p.GetCompilers(options)).ToList();
      var backend = backends.LastOrDefault(c => c.TargetId == options.CompilerName);
      if (backend == null) {
        if (options.CompilerName != null) {
          var known = String.Join(", ", backends.Select(c => $"'{c.TargetId}' ({c.TargetName})"));
          options.ErrorWriter.WriteLine(
            $"*** Error: No compiler found for target \"{options.CompilerName}\"{(options.CompilerName.StartsWith("-t") || options.CompilerName.StartsWith("--") ? " (use just a target name, not a -t or --target option)" : "")}; expecting one of {known}");
        } else {
          backend = new NoExecutableBackend(options);
        }
      }

      return backend;
    }

    public async Task<ExitValue> ProcessFilesAsync(IReadOnlyList<DafnyFile/*!*/>/*!*/ dafnyFiles,
      ReadOnlyCollection<string> otherFileNames,
      DafnyOptions options, ProofDependencyManager depManager,
      bool lookForSnapshots = true, string programId = null) {
      Contract.Requires(Cce.NonNullElements(dafnyFiles));
      var dafnyFileNames = DafnyFile.FileNames(dafnyFiles);

      ExitValue exitValue = ExitValue.SUCCESS;

      if (options.VerifySeparately && 1 < dafnyFiles.Count) {
        foreach (var f in dafnyFiles) {
          await options.OutputWriter.Status($"-------------------- {f} --------------------");
          var ev = await ProcessFilesAsync(new List<DafnyFile> { f }, new List<string>().AsReadOnly(), options, depManager, lookForSnapshots, f.FilePath);
          if (exitValue != ev && ev != ExitValue.SUCCESS) {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      if (0 < options.VerifySnapshots && lookForSnapshots) {
        var snapshotsByVersion = ExecutionEngine.LookForSnapshots(dafnyFileNames);
        foreach (var s in snapshotsByVersion) {
          var snapshots = new List<DafnyFile>();
          foreach (var f in s) {
            var uri = new Uri(Path.GetFullPath(f));
            snapshots.Add(DafnyFile.HandleDafnyFile(OnDiskFileSystem.Instance, new ConsoleErrorReporter(options), options, uri, Token.Cli));
            options.CliRootSourceUris.Add(uri);
          }
          var ev = await ProcessFilesAsync(snapshots, new List<string>().AsReadOnly(), options, depManager, false, programId);
          if (exitValue != ev && ev != ExitValue.SUCCESS) {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      string programName = dafnyFileNames.Count == 1 ? dafnyFileNames[0] : "the_program";
      var (dafnyProgram, err) = await DafnyMain.ParseCheck(options.Input, dafnyFiles, programName, options);
      if (err != null) {
        exitValue = ExitValue.DAFNY_ERROR;
        await options.OutputWriter.Status(err);
      } else if (dafnyProgram != null && !options.NoResolve && !options.NoTypecheck) {

        bool verified;
        PipelineOutcome outcome;
        IDictionary<string, PipelineStatistics> moduleStats;
        dafnyProgram.ProofDependencyManager = depManager;
        if (!options.DafnyVerify) {
          verified = false;
          outcome = PipelineOutcome.Done;
          moduleStats = new Dictionary<string, PipelineStatistics>();
        } else {
          var boogiePrograms =
            await DafnyMain.LargeStackFactory.StartNew(() => Translate(engine.Options, dafnyProgram).ToList());

          string baseName = Cce.NonNull(Path.GetFileName(dafnyFileNames[^1]));
          (verified, outcome, moduleStats) =
            await BoogieAsync(dafnyProgram.Reporter, options, baseName, boogiePrograms, programId);

          if (options.TrackVerificationCoverage) {
            ProofDependencyWarnings.WarnAboutSuspiciousDependenciesUsingStoredPartialResults(options,
              dafnyProgram.Reporter, depManager);
            var coverageReportDir = options.Get(CommonOptionBag.VerificationCoverageReport);
            if (coverageReportDir != null) {
              await new CoverageReporter(options).SerializeVerificationCoverageReport(
                depManager, dafnyProgram,
                boogiePrograms.SelectMany(tp => tp.Item2.AllCoveredElements),
                coverageReportDir);
            }
          }
        }

        bool compiled;
        try {
          compiled = await Compile(dafnyFileNames[0], otherFileNames, dafnyProgram, outcome, moduleStats, verified);
        } catch (UnsupportedFeatureException e) {
          if (!options.Backend.UnsupportedFeatures.Contains(e.Feature)) {
            throw new Exception(
              $"'{e.Feature}' is not an element of the {options.Backend.TargetId} compiler's UnsupportedFeatures set");
          }

          dafnyProgram.Reporter.Error(MessageSource.Compiler, GeneratorErrors.ErrorId.f_unsupported_feature, e.Token,
            e.Message);
          compiled = false;
        } catch (UnsupportedInvalidOperationException e) {
          // Not having this catch makes all tests running for all compilers take 10-15x longer on Windows,
          // just because of the Dafny compiler.
          dafnyProgram.Reporter.Error(MessageSource.Compiler, GeneratorErrors.ErrorId.f_unsupported_feature, e.Token, e.Message);
          compiled = false;
        }

        var failBecauseOfDiagnostics = dafnyProgram.Reporter.FailCompilationMessage;
        if (!verified && options.DafnyVerify) {
          exitValue = ExitValue.VERIFICATION_ERROR;
        } else if (!compiled) {
          exitValue = ExitValue.COMPILE_ERROR;
        } else if (failBecauseOfDiagnostics != null) {
          exitValue = ExitValue.DAFNY_ERROR;
          await options.OutputWriter.Status($"Returning exit code {exitValue} because {failBecauseOfDiagnostics}");
        }
      }

      if (err == null && dafnyProgram != null && options.PrintStats) {
        await Util.PrintStats(dafnyProgram);
      }
      if (err == null && dafnyProgram != null && options.PrintFunctionCallGraph) {
        await Util.PrintFunctionCallGraph(dafnyProgram);
      }
      if (dafnyProgram != null && options.ExtractCounterexample && exitValue == ExitValue.VERIFICATION_ERROR) {
        await PrintCounterexample(options);
      }

      return exitValue;
    }

    /// <summary>
    /// Extract the counterexample corresponding to the first failing
    /// assertion and print it to the console
    /// </summary>
    private static async Task PrintCounterexample(DafnyOptions options) {
      var firstCounterexample = ((DafnyConsolePrinter)options.Printer).VerificationResults
        .Select(result => result.Result)
        .Where(result => result.Outcome == VcOutcome.Errors)
        .Select(result => result.Counterexamples)
        .Where(counterexampleList => counterexampleList != null)
        .Select(counterexampleList => counterexampleList.FirstOrDefault(counterexample => counterexample.Model != null))
        .FirstOrDefault(counterexample => counterexample != null);
      if (firstCounterexample == null) {
        return;
      }
      var model = new DafnyModel(firstCounterexample.Model, options);
      await options.OutputWriter.Status($"The following counterexample refers to the following failing assertion:\n{model.ToString()}");
    }

    private static string BoogieProgramSuffix(string printFile, string suffix) {
      var baseName = Path.GetFileNameWithoutExtension(printFile);
      var dirName = Path.GetDirectoryName(printFile);

      return Path.Combine(dirName, baseName + "_" + suffix + Path.GetExtension(printFile));
    }

    public static IEnumerable<Tuple<string, Bpl.Program>> Translate(ExecutionEngineOptions options, Program dafnyProgram) {
      var modulesCount = BoogieGenerator.VerifiableModules(dafnyProgram).Count();


      foreach (var prog in BoogieGenerator.Translate(dafnyProgram, dafnyProgram.Reporter)) {

        if (options.PrintFile != null) {

          var fileName = modulesCount > 1 ? Dafny.DafnyMain.BoogieProgramSuffix(options.PrintFile, prog.Item1) : options.PrintFile;

          ExecutionEngine.PrintBplFile(options, fileName, prog.Item2, false, false, options.PrettyPrint);
        }

        yield return prog;

      }
    }

    public async Task<(bool IsVerified, PipelineOutcome Outcome, IDictionary<string, PipelineStatistics> ModuleStats)>
      BoogieAsync(
        ErrorReporter errorReporter,
        DafnyOptions options,
        string baseName,
        IEnumerable<Tuple<string, Bpl.Program>> boogiePrograms, string programId) {
      var concurrentModuleStats = new ConcurrentDictionary<string, PipelineStatistics>();
      await using var sw = options.OutputWriter.StatusWriter();
      var writerManager = new ConcurrentToSequentialWriteManager(sw);

      if (options.Verify || options.Get(BoogieOptionBag.HiddenNoVerify)) {
        var before = errorReporter.ErrorCount;
        options.ProcessSolverOptions(errorReporter, Token.Cli);
        if (before != errorReporter.ErrorCount) {
          return (false, PipelineOutcome.FatalError, concurrentModuleStats);
        }
      }

      var moduleTasks = boogiePrograms.Select(async program => {
        await using var moduleWriter = writerManager.AppendWriter();
        // ReSharper disable once AccessToDisposedClosure
        var result = await Task.Run(() =>
          BoogieOnceWithTimerAsync(errorReporter, moduleWriter, options, baseName, programId, program.Item1, program.Item2));
        concurrentModuleStats.TryAdd(program.Item1, result.Stats);
        return result;
      }).ToList();

      await Task.WhenAll(moduleTasks);
      var outcome = moduleTasks.Select(t => t.Result.Outcome)
        .Aggregate(PipelineOutcome.VerificationCompleted, MergeOutcomes);

      var isVerified = moduleTasks.Select(t =>
        DafnyMain.IsBoogieVerified(t.Result.Outcome, t.Result.Stats)).All(x => x);
      return (isVerified, outcome, concurrentModuleStats);
    }

    private async Task<(PipelineOutcome Outcome, PipelineStatistics Stats)> BoogieOnceWithTimerAsync(
      ErrorReporter errorReporter,
      TextWriter output,
      DafnyOptions options,
      string baseName, string programId,
      string moduleName,
      Bpl.Program program) {
      Stopwatch watch = new Stopwatch();
      watch.Start();
      if (options.SeparateModuleOutput) {
        options.Printer.AdvisoryWriteLine(output, "For module: {0}", moduleName);
      }

      var result =
        await await DafnyMain.LargeStackFactory.StartNew(() => DafnyMain.BoogieOnce(errorReporter, options, output, engine, baseName, moduleName, program, programId));

      watch.Stop();

      if (options.SeparateModuleOutput) {
        TimeSpan ts = watch.Elapsed;
        string elapsedTime = $"{ts.Hours:00}:{ts.Minutes:00}:{ts.Seconds:00}";
        options.Printer.AdvisoryWriteLine(output, "Elapsed time: {0}", elapsedTime);
        WriteTrailer(options, output, result.Statistics);
      }

      return result;
    }

    private static PipelineOutcome MergeOutcomes(PipelineOutcome first, PipelineOutcome second) {

      if ((first == PipelineOutcome.VerificationCompleted || first == PipelineOutcome.Done) &&
          second != PipelineOutcome.VerificationCompleted) {
        return second;
      }

      return first;
    }

    public static void WriteTrailer(DafnyOptions options, TextWriter output, PipelineStatistics stats) {
      if (!options.Verify && stats.ErrorCount == 0) {
        output.WriteLine();
        output.Write("{0} did not attempt verification", options.DescriptiveToolName);
        if (stats.InconclusiveCount != 0) {
          output.Write(", {0} inconclusive{1}", stats.InconclusiveCount, Util.Plural(stats.InconclusiveCount));
        }
        if (stats.TimeoutCount != 0) {
          output.Write(", {0} time out{1}", stats.TimeoutCount, Util.Plural(stats.TimeoutCount));
        }
        if (stats.OutOfMemoryCount != 0) {
          output.Write(", {0} out of memory", stats.OutOfMemoryCount);
        }
        if (stats.OutOfResourceCount != 0) {
          output.Write(", {0} out of resource", stats.OutOfResourceCount);
        }
        if (stats.SolverExceptionCount != 0) {
          output.Write(", {0} solver exceptions", stats.SolverExceptionCount);
        }

        output.WriteLine();
        output.Flush();
      } else {
        // This calls a routine within Boogie
        options.Printer.WriteTrailer(output, stats);
      }
    }

    public static void WriteProgramVerificationSummary(DafnyOptions options, IDafnyOutputWriter output, IDictionary<string, PipelineStatistics> moduleStats) {
      var statSum = new PipelineStatistics();
      foreach (var stats in moduleStats) {
        statSum.VerifiedCount += stats.Value.VerifiedCount;
        statSum.ErrorCount += stats.Value.ErrorCount;
        statSum.TimeoutCount += stats.Value.TimeoutCount;
        statSum.OutOfResourceCount += stats.Value.OutOfResourceCount;
        statSum.OutOfMemoryCount += stats.Value.OutOfMemoryCount;
        statSum.SolverExceptionCount += stats.Value.SolverExceptionCount;
        statSum.CachedErrorCount += stats.Value.CachedErrorCount;
        statSum.CachedInconclusiveCount += stats.Value.CachedInconclusiveCount;
        statSum.CachedOutOfMemoryCount += stats.Value.CachedOutOfMemoryCount;
        statSum.CachedTimeoutCount += stats.Value.CachedTimeoutCount;
        statSum.CachedOutOfResourceCount += stats.Value.CachedOutOfResourceCount;
        statSum.CachedSolverExceptionCount += stats.Value.CachedSolverExceptionCount;
        statSum.CachedVerifiedCount += stats.Value.CachedVerifiedCount;
        statSum.InconclusiveCount += stats.Value.InconclusiveCount;
      }

      using var tw = output.StatusWriter();
      WriteTrailer(options, tw, statSum);
    }


    public static async Task<bool> Compile(string fileName, ReadOnlyCollection<string> otherFileNames, Program dafnyProgram,
                               PipelineOutcome oc, IDictionary<string, PipelineStatistics> moduleStats, bool verified) {
      var options = dafnyProgram.Options;
      var resultFileName = options.DafnyPrintCompiledFile ?? fileName;
      bool compiled = true;
      switch (oc) {
        case PipelineOutcome.VerificationCompleted:
          WriteProgramVerificationSummary(options, options.OutputWriter, moduleStats);
          if ((options.Compile && verified && !options.UserConstrainedProcsToCheck) || options.ForceCompile) {
            compiled = await CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, true);
          } else if ((2 <= options.SpillTargetCode && verified && !options.UserConstrainedProcsToCheck) || 3 <= options.SpillTargetCode) {
            compiled = await CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, false);
          }
          break;
        case PipelineOutcome.Done:
          WriteProgramVerificationSummary(options, options.OutputWriter, moduleStats);
          if (options.ForceCompile || 3 <= options.SpillTargetCode) {
            compiled = await CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, options.ForceCompile);
          }
          break;
        default:
          // error has already been reported to user
          break;
      }
      return compiled;
    }

    #region Compilation

    private record TargetPaths(string Directory, string Filename) {
      private static Func<string, string> DeleteDot = p => p == "." ? "" : p;
      private static Func<string, string> AddDot = p => p == "" ? "." : p;
      private Func<string, string> RelativeToDirectory =
        path => DeleteDot(Path.GetRelativePath(AddDot(Directory), path));

      public string RelativeDirectory => RelativeToDirectory(AddDot(Path.GetDirectoryName(Filename)));
      public string RelativeFilename => RelativeToDirectory(Filename);
      public string SourceDirectory => Path.GetDirectoryName(Filename);
    }

    private static TargetPaths GenerateTargetPaths(DafnyOptions options, string dafnyProgramName) {
      string targetBaseDir = options.Backend.TargetBaseDir(dafnyProgramName);
      string targetExtension = options.Backend.TargetExtension;

      // Note that using Path.ChangeExtension here does the wrong thing when dafnyProgramName has multiple periods (e.g., a.b.dfy)
      string targetBaseName = options.Backend.TargetBasename(dafnyProgramName) + "." + targetExtension;
      string targetDir = Path.Combine(Path.GetDirectoryName(dafnyProgramName), targetBaseDir);

      string targetFilename = Path.Combine(targetDir, targetBaseName);

      return new TargetPaths(Directory: Path.GetDirectoryName(dafnyProgramName), Filename: targetFilename);
    }

    static async Task WriteDafnyProgramToFiles(DafnyOptions options, TargetPaths paths, bool targetProgramHasErrors, string targetProgramText,
      string/*?*/ callToMain, Dictionary<string, string> otherFiles, IDafnyOutputWriter outputWriter) {
      if (targetProgramText.Length != 0) {
        WriteFile(paths.Filename, targetProgramText, callToMain);
      }

      string NormalizeRelativeFilename(string fileName) {
        return RuntimeInformation.IsOSPlatform(OSPlatform.Windows)
          ? fileName.Replace(@"\", "/")
          : fileName;
      }

      var relativeTarget = NormalizeRelativeFilename(paths.RelativeFilename);
      if (targetProgramHasErrors) {
        // Something went wrong during compilation (e.g., the compiler may have found an "assume" statement).
        // As a courtesy, we're still printing the text of the generated target program. We print a message regardless
        // of the Verbose settings.
        await outputWriter.Status($"Wrote textual form of partial target program to {relativeTarget}");
      } else if (options.Verbose) {
        await outputWriter.Status($"Wrote textual form of target program to {relativeTarget}");
      }

      foreach (var (filename, value) in otherFiles) {
        var absoluteFilename = Path.IsPathRooted(filename) ? filename : Path.Join(paths.SourceDirectory, filename);
        WriteFile(absoluteFilename, value);
        if (options.Verbose) {
          await outputWriter.Status($"Additional output written to {NormalizeRelativeFilename(Path.Join(paths.RelativeDirectory, filename))}");
        }
      }
    }

    public static void WriteFile(string filename, string text, string moreText = null) {
      var dir = Path.GetDirectoryName(filename);
      if (dir != "") {
        Directory.CreateDirectory(dir);
      }

      CheckFilenameIsLegal(filename);
      using TextWriter target = new StreamWriter(new FileStream(filename, FileMode.Create));
      target.Write(text);
      if (moreText != null) {
        target.Write(moreText);
      }
    }

    private static void CheckFilenameIsLegal(string filename) {
      // We cannot get the full path correctly on Windows if the file name uses some reserved words
      // For example, Path.GetFullPath("con.txt") will return "//./con" which is incorrect.
      // https://docs.microsoft.com/en-us/windows/win32/fileio/naming-a-file?redirectedfrom=MSDN
      if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
        var problematicNames =
          "CON, PRN, AUX, NUL, COM1, COM2, COM3, COM4, COM5, COM6, COM7, COM8, COM9, LPT1, LPT2, LPT3, LPT4, LPT5, LPT6, LPT7, LPT8, LPT9";
        var problematicRegex =
          new Regex(@"^(.*[/\\]|^)(" +
                    string.Join("|", problematicNames.Split(", ")) + @")(\.[^/\\]*)?$", RegexOptions.IgnoreCase);
        var match = problematicRegex.Match(filename);
        if (match.Success) {
          throw new Exception($"Cannot create a file with the name {filename}." +
                              $" Windows reserves the following file names: {problematicNames}");
        }
      }
    }

    /// <summary>
    /// Generate a target language program from the Dafny program and, if "invokeCompiler" is "true", invoke
    /// the target language compiler to compile it.
    /// </summary>
    public static async Task<bool> CompileDafnyProgram(Program dafnyProgram, string dafnyProgramName,
                                           ReadOnlyCollection<string> otherFileNames, bool invokeCompiler) {
      var rewriters = RewriterCollection.GetRewriters(dafnyProgram.Reporter, dafnyProgram);
      foreach (var rewriter in rewriters) {
        rewriter.PostVerification(dafnyProgram);
      }

      Contract.Requires(dafnyProgram != null);
      Contract.Assert(dafnyProgramName != null);

      var outputWriter = dafnyProgram.Options.OutputWriter;
      var errorWriter = dafnyProgram.Options.ErrorWriter;

      // Compile the Dafny program into a string that contains the target program
      var oldErrorCount = dafnyProgram.Reporter.Count(ErrorLevel.Error);
      var options = dafnyProgram.Options;

      var compiler = options.Backend;
      compiler.OnPreCompile(dafnyProgram.Reporter, otherFileNames);

      // Now that an internal compiler is instantiated, apply any plugin instrumentation.
      foreach (var compilerInstrumenter in options.Plugins.SelectMany(p => p.GetCompilerInstrumenters(dafnyProgram.Reporter))) {
        compiler.InstrumentCompiler(compilerInstrumenter, dafnyProgram);
      }

      if (options.Get(CommonOptionBag.ExecutionCoverageReport) != null
          && compiler.UnsupportedFeatures.Contains(Feature.RuntimeCoverageReport)) {
        throw new UnsupportedFeatureException(dafnyProgram.GetStartOfFirstFileToken(), Feature.RuntimeCoverageReport);
      }

      var hasMain = SinglePassCodeGenerator.HasMain(dafnyProgram, out var mainMethod);
      if (hasMain) {
        mainMethod.IsEntryPoint = true;
        dafnyProgram.MainMethod = mainMethod;
      }
      string targetProgramText;
      var otherFiles = new Dictionary<string, string>();
      {
        var output = new ConcreteSyntaxTree();

        await DafnyMain.LargeStackFactory.StartNew(() => compiler.Compile(dafnyProgram, dafnyProgramName, output));

        var writerOptions = new WriterState();
        var targetProgramTextWriter = new StringWriter();
        var files = new Queue<FileSyntax>();
        output.Render(targetProgramTextWriter, 0, writerOptions, files, compiler.TargetIndentSize);
        targetProgramText = targetProgramTextWriter.ToString();

        while (files.Count > 0) {
          var file = files.Dequeue();
          var otherFileWriter = new StringWriter();
          writerOptions.HasNewLine = false;
          file.Tree.Render(otherFileWriter, 0, writerOptions, files, compiler.TargetIndentSize);
          otherFiles.Add(file.Filename, otherFileWriter.ToString());
        }
      }
      string callToMain = null;
      if (hasMain) {
        var callToMainTree = new ConcreteSyntaxTree();
        string baseName = Path.GetFileNameWithoutExtension(dafnyProgramName);
        compiler.EmitCallToMain(mainMethod, baseName, callToMainTree);
        callToMain = callToMainTree.MakeString(compiler.TargetIndentSize); // assume there aren't multiple files just to call main
      }
      Contract.Assert(hasMain == (callToMain != null));
      bool targetProgramHasErrors = dafnyProgram.Reporter.Count(ErrorLevel.Error) != oldErrorCount;

      var targetPaths = GenerateTargetPaths(options, dafnyProgramName);
      if (dafnyProgram.Reporter.FailCompilation) {
        await dafnyProgram.Options.OutputWriter.Status($"Translation was aborted because {dafnyProgram.Reporter.FailCompilationMessage}");
        return false;
      }
      // blurt out the code to a file, if requested, or if other target-language files were specified on the command line.
      if (options.SpillTargetCode > 0 || otherFileNames.Count > 0 || (invokeCompiler && !compiler.SupportsInMemoryCompilation) ||
          (invokeCompiler && compiler.TextualTargetIsExecutable && !options.RunAfterCompile)) {
        compiler.CleanSourceDirectory(targetPaths.SourceDirectory);
        await WriteDafnyProgramToFiles(options, targetPaths, targetProgramHasErrors, targetProgramText, callToMain, otherFiles, outputWriter);
      }

      var postGenerateFailed = !await compiler.OnPostGenerate(dafnyProgramName, targetPaths.SourceDirectory, outputWriter);
      if (postGenerateFailed) {
        return false;
      }

      // If we got here, compilation succeeded
      if (!invokeCompiler) {
        return true; // If we're not asked to invoke the target compiler, we can report success
      }

      // compile the program into an assembly
      var (compiledCorrectly, compilationResult) = await compiler.CompileTargetProgram(dafnyProgramName,
        targetProgramText, callToMain, targetPaths.Filename, otherFileNames,
        hasMain && options.RunAfterCompile, outputWriter);
      if (compiledCorrectly && options.RunAfterCompile) {
        if (hasMain) {
          if (options.Verbose) {
            await outputWriter.Status("Running...\n");
          }

          compiledCorrectly = await compiler.RunTargetProgram(dafnyProgramName, targetProgramText, callToMain,
            targetPaths.Filename, otherFileNames, compilationResult, outputWriter);

          if (compiledCorrectly) {
            var coverageReportDir = options.Get(CommonOptionBag.ExecutionCoverageReport);
            if (coverageReportDir != null) {
              var coverageReport = new CoverageReport("Execution Coverage", "Branches", "_tests_actual", dafnyProgram);
              compiler.PopulateCoverageReport(coverageReport);
              await new CoverageReporter(options).SerializeCoverageReports(coverageReport, coverageReportDir);
            }
          }
        } else {
          // make sure to give some feedback to the user
          if (options.Verbose) {
            await outputWriter.Status("Program compiled successfully");
          }
        }
      }
      return compiledCorrectly;
    }

    #endregion

    public void Dispose() {
      engine.Dispose();
    }
  }
}
