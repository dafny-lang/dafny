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

using DafnyServer.CounterexampleGeneration;

namespace Microsoft.Dafny {
  using System;
  using System.Collections.Generic;
  using System.Collections.ObjectModel;
  using System.Diagnostics.Contracts;
  using System.IO;
  using System.Linq;

  using Microsoft.Boogie;
  using Bpl = Microsoft.Boogie;
  using System.Diagnostics;

  public class DafnyDriver {
    // TODO: Refactor so that non-errors (NOT_VERIFIED, DONT_PROCESS_FILES) don't result in non-zero exit codes
    public enum ExitValue { SUCCESS = 0, PREPROCESSING_ERROR, DAFNY_ERROR, COMPILE_ERROR, VERIFICATION_ERROR }

    public static int Main(string[] args) {
      int ret = 0;
      var thread = new System.Threading.Thread(
        new System.Threading.ThreadStart(() => { ret = ThreadMain(args); }),
          0x10000000); // 256MB stack size to prevent stack overflow
      thread.Start();
      thread.Join();
      return ret;
    }

    public static int ThreadMain(string[] args) {
      Contract.Requires(cce.NonNullElements(args));

      ErrorReporter reporter = new ConsoleErrorReporter();
      ExecutionEngine.printer = new DafnyConsolePrinter(); // For boogie errors

      DafnyOptions.Install(new DafnyOptions(reporter));

      CommandLineArgumentsResult cliArgumentsResult = ProcessCommandLineArguments(args, out var dafnyFiles, out var otherFiles);
      ExitValue exitValue;
      switch (cliArgumentsResult) {
        case CommandLineArgumentsResult.OK:
          exitValue = ProcessFiles(dafnyFiles, otherFiles.AsReadOnly(), reporter);
          break;
        case CommandLineArgumentsResult.PREPROCESSING_ERROR:
          exitValue = ExitValue.PREPROCESSING_ERROR;
          break;
        case CommandLineArgumentsResult.OK_EXIT_EARLY:
          exitValue = ExitValue.SUCCESS;
          break;
        default:
          throw new ArgumentOutOfRangeException();
      }

      if (CommandLineOptions.Clo.XmlSink != null) {
        CommandLineOptions.Clo.XmlSink.Close();
        if (DafnyOptions.O.VerificationLoggerConfig != null) {
          BoogieXmlConvertor.RaiseTestLoggerEvents(DafnyOptions.O.BoogieXmlFilename, DafnyOptions.O.VerificationLoggerConfig);
        }
      }
      if (CommandLineOptions.Clo.Wait) {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }
      if (!DafnyOptions.O.CountVerificationErrors) {
        return 0;
      }
      //Console.ReadKey();
      return (int)exitValue;
    }

    public enum CommandLineArgumentsResult {
      /// Indicates that arguments were parsed successfully.
      OK,
      /// Indicates that arguments were not parsed successfully.
      PREPROCESSING_ERROR,
      /// Indicates that arguments were parsed successfully, but the program should exit without processing files.
      OK_EXIT_EARLY
    }

    public static CommandLineArgumentsResult ProcessCommandLineArguments(string[] args, out List<DafnyFile> dafnyFiles, out List<string> otherFiles) {
      dafnyFiles = new List<DafnyFile>();
      otherFiles = new List<string>();

      CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;
      try {
        if (!CommandLineOptions.Clo.Parse(args)) {
          return CommandLineArgumentsResult.PREPROCESSING_ERROR;
        }
      } catch (ProverException pe) {
        ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** ProverException: {0}", pe.Message);
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }

      // If requested, print version number, help, attribute help, etc. and exit.
      if (DafnyOptions.O.ProcessInfoFlags()) {
        return CommandLineArgumentsResult.OK_EXIT_EARLY;
      }

      if (DafnyOptions.O.UseStdin) {
        dafnyFiles.Add(new DafnyFile("<stdin>", true));
      } else if (CommandLineOptions.Clo.Files.Count == 0) {
        ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: No input files were specified.");
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }
      if (CommandLineOptions.Clo.XmlSink != null) {
        string errMsg = CommandLineOptions.Clo.XmlSink.Open();
        if (errMsg != null) {
          ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: " + errMsg);
          return CommandLineArgumentsResult.PREPROCESSING_ERROR;
        }
      }
      if (CommandLineOptions.Clo.ShowEnv == CommandLineOptions.ShowEnvironment.Always) {
        Console.WriteLine("---Command arguments");
        foreach (string arg in args) {
          Contract.Assert(arg != null);
          Console.WriteLine(arg);
        }
        Console.WriteLine("--------------------");
      }

      ISet<String> filesSeen = new HashSet<string>();
      foreach (string file in CommandLineOptions.Clo.Files) {
        Contract.Assert(file != null);
        string extension = Path.GetExtension(file);
        if (extension != null) { extension = extension.ToLower(); }

        bool isDafnyFile = false;
        try {
          var df = new DafnyFile(file);
          if (!filesSeen.Add(df.CanonicalPath)) {
            continue; // silently ignore duplicate
          }
          dafnyFiles.Add(df);
          isDafnyFile = true;
        } catch (IllegalDafnyFile) {
          // Fall through and try to handle the file as an "other file"
        }

        if (DafnyOptions.O.CompileTarget == DafnyOptions.CompilationTarget.Csharp) {
          if (extension == ".cs" || extension == ".dll") {
            otherFiles.Add(file);
          } else if (!isDafnyFile) {
            if (extension == "" && file.Length > 0 && (file[0] == '/' || file[0] == '-')) {
              ExecutionEngine.printer.ErrorWriteLine(Console.Out,
                "*** Error: Command-line argument '{0}' is neither a recognized option nor a filename with a supported extension (.dfy, .cs, .dll).",
                file);
            } else {
              ExecutionEngine.printer.ErrorWriteLine(Console.Out,
                "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy) or C# files (.cs) or managed DLLS (.dll)",
                file,
                extension == null ? "" : extension);
            }
            return CommandLineArgumentsResult.PREPROCESSING_ERROR;
          }
        } else if (DafnyOptions.O.CompileTarget == DafnyOptions.CompilationTarget.JavaScript) {
          if (extension == ".js") {
            otherFiles.Add(file);
          } else if (!isDafnyFile) {
            ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy) or JavaScript files (.js)", file,
              extension == null ? "" : extension);
            return CommandLineArgumentsResult.PREPROCESSING_ERROR;
          }
        } else if (DafnyOptions.O.CompileTarget == DafnyOptions.CompilationTarget.Java) {
          if (extension == ".java") {
            otherFiles.Add(file);
          } else if (!isDafnyFile) {
            ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy) or Java files (.java)", file,
              extension == null ? "" : extension);
            return CommandLineArgumentsResult.PREPROCESSING_ERROR;
          }
        } else if (DafnyOptions.O.CompileTarget == DafnyOptions.CompilationTarget.Cpp) {
          if (extension == ".h") {
            otherFiles.Add(file);
          } else if (!isDafnyFile) {
            ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy) or C headers (.h)", file,
              extension == null ? "" : extension);
            return CommandLineArgumentsResult.PREPROCESSING_ERROR;
          }
        } else if (DafnyOptions.O.CompileTarget == DafnyOptions.CompilationTarget.Php) {
          if (extension == ".php") {
            otherFiles.Add(file);
          } else if (!isDafnyFile) {
            ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy) or PHP files (.php)", file,
              extension == null ? "" : extension);
            return CommandLineArgumentsResult.PREPROCESSING_ERROR;
          }
        } else {
          if (extension == ".go") {
            otherFiles.Add(file);
          } else if (!isDafnyFile) {
            ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy) or Go files (.go)", file,
              extension == null ? "" : extension);
            return CommandLineArgumentsResult.PREPROCESSING_ERROR;
          }
        }
      }
      if (dafnyFiles.Count == 0) {
        ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files");
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }

      if (dafnyFiles.Count > 1 &&
          DafnyOptions.O.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
        ExecutionEngine.printer.ErrorWriteLine(Console.Out,
          "*** Error: Only one .dfy file can be specified for testing");
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }

      if (DafnyOptions.O.ExtractCounterexample && DafnyOptions.O.ModelViewFile == null) {
        ExecutionEngine.printer.ErrorWriteLine(Console.Out,
          "*** Error: ModelView file must be specified when attempting counterexample extraction");
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }
      return CommandLineArgumentsResult.OK;
    }

    static ExitValue ProcessFiles(IList<DafnyFile/*!*/>/*!*/ dafnyFiles, ReadOnlyCollection<string> otherFileNames,
                                  ErrorReporter reporter, bool lookForSnapshots = true, string programId = null) {
      Contract.Requires(cce.NonNullElements(dafnyFiles));
      var dafnyFileNames = DafnyFile.fileNames(dafnyFiles);

      ExitValue exitValue = ExitValue.SUCCESS;
      if (DafnyOptions.O.TestGenOptions.WarnDeadCode) {
        foreach (var line in DafnyTestGeneration.Main
          .GetDeadCodeStatistics(dafnyFileNames[0])) {
          Console.WriteLine(line);
        }
        return exitValue;
      }
      if (DafnyOptions.O.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
        foreach (var line in DafnyTestGeneration.Main
          .GetTestClassForProgram(dafnyFileNames[0])) {
          Console.WriteLine(line);
        }
        return exitValue;
      }

      if (CommandLineOptions.Clo.VerifySeparately && 1 < dafnyFiles.Count) {
        foreach (var f in dafnyFiles) {
          Console.WriteLine();
          Console.WriteLine("-------------------- {0} --------------------", f);
          var ev = ProcessFiles(new List<DafnyFile> { f }, new List<string>().AsReadOnly(), reporter, lookForSnapshots, f.FilePath);
          if (exitValue != ev && ev != ExitValue.SUCCESS) {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      if (0 <= CommandLineOptions.Clo.VerifySnapshots && lookForSnapshots) {
        var snapshotsByVersion = ExecutionEngine.LookForSnapshots(dafnyFileNames);
        foreach (var s in snapshotsByVersion) {
          var snapshots = new List<DafnyFile>();
          foreach (var f in s) {
            snapshots.Add(new DafnyFile(f));
          }
          var ev = ProcessFiles(snapshots, new List<string>().AsReadOnly(), reporter, false, programId);
          if (exitValue != ev && ev != ExitValue.SUCCESS) {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      Dafny.Program dafnyProgram;
      string programName = dafnyFileNames.Count == 1 ? dafnyFileNames[0] : "the_program";
      string err = Dafny.Main.ParseCheck(dafnyFiles, programName, reporter, out dafnyProgram);
      if (err != null) {
        exitValue = ExitValue.DAFNY_ERROR;
        ExecutionEngine.printer.ErrorWriteLine(Console.Out, err);
      } else if (dafnyProgram != null && !CommandLineOptions.Clo.NoResolve && !CommandLineOptions.Clo.NoTypecheck
          && DafnyOptions.O.DafnyVerify) {

        var boogiePrograms = Translate(dafnyProgram);

        Dictionary<string, PipelineStatistics> statss;
        PipelineOutcome oc;
        string baseName = cce.NonNull(Path.GetFileName(dafnyFileNames[dafnyFileNames.Count - 1]));
        var verified = Boogie(baseName, boogiePrograms, programId, out statss, out oc);
        var compiled = Compile(dafnyFileNames[0], otherFileNames, dafnyProgram, oc, statss, verified);
        exitValue = verified && compiled ? ExitValue.SUCCESS : !verified ? ExitValue.VERIFICATION_ERROR : ExitValue.COMPILE_ERROR;
      }

      if (err == null && dafnyProgram != null && DafnyOptions.O.PrintStats) {
        Util.PrintStats(dafnyProgram);
      }
      if (err == null && dafnyProgram != null && DafnyOptions.O.PrintFunctionCallGraph) {
        Util.PrintFunctionCallGraph(dafnyProgram);
      }
      if (dafnyProgram != null && DafnyOptions.O.ExtractCounterexample && exitValue == ExitValue.VERIFICATION_ERROR) {
        PrintCounterexample(DafnyOptions.O.ModelViewFile);
      }
      return exitValue;
    }

    /// <summary>
    /// Extract the counterexample corresponding to the first failing
    /// assertion and print it to the console
    /// </summary>
    /// <param name="modelViewFile"> Name of the file from which to read
    /// the counterexample </param> 
    private static void PrintCounterexample(string modelViewFile) {
      var model = DafnyModel.ExtractModel(File.ReadAllText(modelViewFile));
      Console.WriteLine("Counterexample for first failing assertion: ");
      foreach (var state in model.States.Where(state => !state.IsInitialState)) {
        Console.WriteLine(state.FullStateName + ":");
        var vars = state.ExpandedVariableSet(-1);
        foreach (var variable in vars) {
          Console.WriteLine($"\t{variable.ShortName} : " +
                            $"{variable.Type.InDafnyFormat()} = " +
                            $"{variable.Value}");
        }
      }
    }

    private static string BoogieProgramSuffix(string printFile, string suffix) {
      var baseName = Path.GetFileNameWithoutExtension(printFile);
      var dirName = Path.GetDirectoryName(printFile);

      return Path.Combine(dirName, baseName + "_" + suffix + Path.GetExtension(printFile));
    }

    public static IEnumerable<Tuple<string, Bpl.Program>> Translate(Program dafnyProgram) {
      var nmodules = Translator.VerifiableModules(dafnyProgram).Count();


      foreach (var prog in Translator.Translate(dafnyProgram, dafnyProgram.reporter)) {

        if (CommandLineOptions.Clo.PrintFile != null) {

          var nm = nmodules > 1 ? BoogieProgramSuffix(CommandLineOptions.Clo.PrintFile, prog.Item1) : CommandLineOptions.Clo.PrintFile;

          ExecutionEngine.PrintBplFile(nm, prog.Item2, false, false, CommandLineOptions.Clo.PrettyPrint);
        }

        yield return prog;

      }
    }

    public static bool BoogieOnce(string baseFile, string moduleName, Bpl.Program boogieProgram, string programId,
                              out PipelineStatistics stats, out PipelineOutcome oc) {
      if (programId == null) {
        programId = "main_program_id";
      }
      programId += "_" + moduleName;

      string bplFilename;
      if (CommandLineOptions.Clo.PrintFile != null) {
        bplFilename = CommandLineOptions.Clo.PrintFile;
      } else {
        string baseName = cce.NonNull(Path.GetFileName(baseFile));
        baseName = cce.NonNull(Path.ChangeExtension(baseName, "bpl"));
        bplFilename = Path.Combine(Path.GetTempPath(), baseName);
      }

      bplFilename = BoogieProgramSuffix(bplFilename, moduleName);
      stats = null;
      oc = BoogiePipelineWithRerun(boogieProgram, bplFilename, out stats, 1 < Dafny.DafnyOptions.Clo.VerifySnapshots ? programId : null);
      return IsBoogieVerified(oc, stats);
    }

    public static bool IsBoogieVerified(PipelineOutcome outcome, PipelineStatistics statistics) {
      return (outcome == PipelineOutcome.Done || outcome == PipelineOutcome.VerificationCompleted)
        && statistics.ErrorCount == 0
        && statistics.InconclusiveCount == 0
        && statistics.TimeoutCount == 0
        && statistics.OutOfResourceCount == 0
        && statistics.OutOfMemoryCount == 0;
    }

    public static bool Boogie(string baseName, IEnumerable<Tuple<string, Bpl.Program>> boogiePrograms, string programId, out Dictionary<string, PipelineStatistics> statss, out PipelineOutcome oc) {

      bool isVerified = true;
      oc = PipelineOutcome.VerificationCompleted;
      statss = new Dictionary<string, PipelineStatistics>();

      Stopwatch watch = new Stopwatch();
      watch.Start();

      foreach (var prog in boogiePrograms) {
        if (DafnyOptions.O.SeparateModuleOutput) {
          ExecutionEngine.printer.AdvisoryWriteLine("For module: {0}", prog.Item1);
        }

        isVerified = BoogieOnce(baseName, prog.Item1, prog.Item2, programId, out var newstats, out var newoc) && isVerified;

        watch.Stop();

        if ((oc == PipelineOutcome.VerificationCompleted || oc == PipelineOutcome.Done) && newoc != PipelineOutcome.VerificationCompleted) {
          oc = newoc;
        }

        if (DafnyOptions.O.SeparateModuleOutput) {
          TimeSpan ts = watch.Elapsed;
          string elapsedTime = $"{ts.Hours:00}:{ts.Minutes:00}:{ts.Seconds:00}";
          ExecutionEngine.printer.AdvisoryWriteLine("Elapsed time: {0}", elapsedTime);
          WriteTrailer(newstats);
        }

        statss.Add(prog.Item1, newstats);
        watch.Restart();
      }
      watch.Stop();

      return isVerified;
    }

    private static void WriteTrailer(PipelineStatistics stats) {
      if (!CommandLineOptions.Clo.Verify && stats.ErrorCount == 0) {
        Console.WriteLine();
        Console.Write("{0} did not attempt verification", CommandLineOptions.Clo.DescriptiveToolName);
        if (stats.InconclusiveCount != 0) {
          Console.Write(", {0} inconclusive{1}", stats.InconclusiveCount, Util.Plural(stats.InconclusiveCount));
        }
        if (stats.TimeoutCount != 0) {
          Console.Write(", {0} time out{1}", stats.TimeoutCount, Util.Plural(stats.TimeoutCount));
        }
        if (stats.OutOfMemoryCount != 0) {
          Console.Write(", {0} out of memory", stats.OutOfMemoryCount);
        }
        if (stats.OutOfResourceCount != 0) {
          Console.Write(", {0} out of resource", stats.OutOfResourceCount);
        }
        Console.WriteLine();
        Console.Out.Flush();
      } else {
        // This calls a routine within Boogie
        ExecutionEngine.printer.WriteTrailer(stats);
      }
    }

    private static void WriteStatss(Dictionary<string, PipelineStatistics> statss) {
      var statSum = new PipelineStatistics();
      foreach (var stats in statss) {
        statSum.VerifiedCount += stats.Value.VerifiedCount;
        statSum.ErrorCount += stats.Value.ErrorCount;
        statSum.TimeoutCount += stats.Value.TimeoutCount;
        statSum.OutOfResourceCount += stats.Value.OutOfResourceCount;
        statSum.OutOfMemoryCount += stats.Value.OutOfMemoryCount;
        statSum.CachedErrorCount += stats.Value.CachedErrorCount;
        statSum.CachedInconclusiveCount += stats.Value.CachedInconclusiveCount;
        statSum.CachedOutOfMemoryCount += stats.Value.CachedOutOfMemoryCount;
        statSum.CachedTimeoutCount += stats.Value.CachedTimeoutCount;
        statSum.CachedOutOfResourceCount += stats.Value.CachedOutOfResourceCount;
        statSum.CachedVerifiedCount += stats.Value.CachedVerifiedCount;
        statSum.InconclusiveCount += stats.Value.InconclusiveCount;
      }
      WriteTrailer(statSum);
    }


    public static bool Compile(string fileName, ReadOnlyCollection<string> otherFileNames, Program dafnyProgram,
                               PipelineOutcome oc, Dictionary<string, PipelineStatistics> statss, bool verified) {
      var resultFileName = DafnyOptions.O.DafnyPrintCompiledFile ?? fileName;
      bool compiled = true;
      switch (oc) {
        case PipelineOutcome.VerificationCompleted:
          WriteStatss(statss);
          if ((DafnyOptions.O.Compile && verified && !CommandLineOptions.Clo.UserConstrainedProcsToCheck) || DafnyOptions.O.ForceCompile) {
            compiled = CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, true);
          } else if (2 <= DafnyOptions.O.SpillTargetCode && verified && !CommandLineOptions.Clo.UserConstrainedProcsToCheck || 3 <= DafnyOptions.O.SpillTargetCode) {
            compiled = CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, false);
          }
          break;
        case PipelineOutcome.Done:
          WriteStatss(statss);
          if (DafnyOptions.O.ForceCompile || 3 <= DafnyOptions.O.SpillTargetCode) {
            compiled = CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, DafnyOptions.O.ForceCompile);
          }
          break;
        default:
          // error has already been reported to user
          break;
      }
      return compiled;
    }

    /// <summary>
    /// Resolve, type check, infer invariants for, and verify the given Boogie program.
    /// The intention is that this Boogie program has been produced by translation from something
    /// else.  Hence, any resolution errors and type checking errors are due to errors in
    /// the translation.
    /// The method prints errors for resolution and type checking errors, but still returns
    /// their error code.
    /// </summary>
    static PipelineOutcome BoogiePipelineWithRerun(Bpl.Program/*!*/ program, string/*!*/ bplFileName,
        out PipelineStatistics stats, string programId) {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out stats).InconclusiveCount && 0 <= Contract.ValueAtReturn(out stats).TimeoutCount);

      stats = new PipelineStatistics();
      CivlTypeChecker ctc;
      PipelineOutcome oc = ExecutionEngine.ResolveAndTypecheck(program, bplFileName, out ctc);
      switch (oc) {
        case PipelineOutcome.Done:
          return oc;

        case PipelineOutcome.ResolutionError:
        case PipelineOutcome.TypeCheckingError: {
            ExecutionEngine.PrintBplFile(bplFileName, program, false, false, CommandLineOptions.Clo.PrettyPrint);
            Console.WriteLine();
            Console.WriteLine("*** Encountered internal translation error - re-running Boogie to get better debug information");
            Console.WriteLine();

            List<string/*!*/>/*!*/ fileNames = new List<string/*!*/>();
            fileNames.Add(bplFileName);
            Bpl.Program reparsedProgram = ExecutionEngine.ParseBoogieProgram(fileNames, true);
            if (reparsedProgram != null) {
              ExecutionEngine.ResolveAndTypecheck(reparsedProgram, bplFileName, out ctc);
            }
          }
          return oc;

        case PipelineOutcome.ResolvedAndTypeChecked:
          ExecutionEngine.EliminateDeadVariables(program);
          ExecutionEngine.CollectModSets(program);
          ExecutionEngine.CoalesceBlocks(program);
          ExecutionEngine.Inline(program);
          return ExecutionEngine.InferAndVerify(program, stats, programId);

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected outcome
      }
    }


    #region Output

    class DafnyConsolePrinter : ConsolePrinter {
      private readonly Dictionary<string, List<string>> fsCache = new Dictionary<string, List<string>>();

      private string GetFileLine(string filename, int lineNumber) {
        List<string> lines;
        if (!fsCache.ContainsKey(filename)) {
          try {
            // Note: This is not guaranteed to be the same file that Dafny parsed. To ensure that, Dafny should keep
            // an in-memory version of each file it parses.
            lines = File.ReadLines(filename).ToList();
          } catch (Exception) {
            lines = new List<string>();
          }
          fsCache.Add(filename, lines);
        } else {
          lines = fsCache[filename];
        }
        if (0 <= lineNumber && lineNumber < lines.Count) {
          return lines[lineNumber];
        }
        return "<nonexistent line>";
      }

      private void WriteSourceCodeSnippet(IToken tok, TextWriter tw) {
        string line = GetFileLine(tok.filename, tok.line - 1);
        string lineNumber = tok.line.ToString();
        string lineNumberSpaces = new string(' ', lineNumber.Length);
        string columnSpaces = new string(' ', tok.col - 1);
        tw.WriteLine($"{lineNumberSpaces} |");
        tw.WriteLine($"{lineNumber      } | {line}");
        tw.WriteLine($"{lineNumberSpaces} | {columnSpaces}^ here");
        tw.WriteLine("");
      }

      public override void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null) {
        // Dafny has 0-indexed columns, but Boogie counts from 1
        var realigned_tok = new Token(tok.line, tok.col - 1);
        realigned_tok.kind = tok.kind;
        realigned_tok.pos = tok.pos;
        realigned_tok.val = tok.val;
        realigned_tok.filename = tok.filename;
        base.ReportBplError(realigned_tok, message, error, tw, category);
        if (DafnyOptions.O.ShowSnippets) {
          WriteSourceCodeSnippet(tok, tw);
        }

        if (tok is Dafny.NestedToken) {
          var nt = (Dafny.NestedToken)tok;
          ReportBplError(nt.Inner, "Related location", false, tw);
        }
      }
    }

    #endregion


    #region Compilation

    private record TargetPaths(string Directory, string Filename) {
      private Func<string, string> DeleteDot = p => p == "." ? "" : p;
      public string RelativeDirectory => DeleteDot(Path.GetRelativePath(Directory, Path.GetDirectoryName(Filename)));
      public string RelativeFilename => DeleteDot(Path.GetRelativePath(Directory, Filename));
      public string SourceDirectory => Path.GetDirectoryName(Filename);
    }

    private static TargetPaths GenerateTargetPaths(Compiler compiler, string dafnyProgramName) {
      string targetExtension;
      string baseName = Path.GetFileNameWithoutExtension(dafnyProgramName);
      string targetBaseDir = "";
      switch (DafnyOptions.O.CompileTarget) {
        case DafnyOptions.CompilationTarget.Csharp:
          targetExtension = "cs";
          break;
        case DafnyOptions.CompilationTarget.JavaScript:
          targetExtension = "js";
          break;
        case DafnyOptions.CompilationTarget.Go:
          targetExtension = "go";
          targetBaseDir = baseName + "-go/src";
          break;
        case DafnyOptions.CompilationTarget.Java:
          targetExtension = "java";
          targetBaseDir = baseName + "-java";
          baseName = compiler.TransformToClassName(baseName);
          break;
        case DafnyOptions.CompilationTarget.Php:
          targetExtension = "php";
          targetBaseDir = baseName;
          break;
        case DafnyOptions.CompilationTarget.Cpp:
          targetExtension = "cpp";
          break;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }

      // Note that using Path.ChangeExtension here does the wrong thing when dafnyProgramName has multiple periods (e.g., a.b.dfy)
      string targetBaseName = baseName + "." + targetExtension;
      string targetDir = Path.Combine(Path.GetDirectoryName(dafnyProgramName), targetBaseDir);

      string targetFilename = Path.Combine(targetDir, targetBaseName);

      return new TargetPaths(Directory: Path.GetDirectoryName(dafnyProgramName), Filename: targetFilename);
    }

    static void WriteDafnyProgramToFiles(TargetPaths paths, bool targetProgramHasErrors, string targetProgramText,
      string/*?*/ callToMain, Dictionary<string, string> otherFiles, TextWriter outputWriter) {
      // WARNING: Make sure that Directory.Delete is only called when the compilation target is Java.
      // If called during C# or JS compilation, you will lose your entire target directory.
      // Purpose is to delete the old generated folder with the Java compilation output and replace all contents.
      if (DafnyOptions.O.CompileTarget is DafnyOptions.CompilationTarget.Java && Directory.Exists(paths.SourceDirectory)) {
        Directory.Delete(paths.SourceDirectory, true);
      }

      WriteFile(paths.Filename, targetProgramText, callToMain);

      if (targetProgramHasErrors) {
        // Something went wrong during compilation (e.g., the compiler may have found an "assume" statement).
        // As a courtesy, we're still printing the text of the generated target program. We print a message regardless
        // of the CompileVerbose settings.
        outputWriter.WriteLine("Wrote textual form of partial target program to {0}", paths.RelativeFilename);
      } else if (DafnyOptions.O.CompileVerbose) {
        outputWriter.WriteLine("Wrote textual form of target program to {0}", paths.RelativeFilename);
      }

      foreach (var entry in otherFiles) {
        var filename = entry.Key;
        WriteFile(Path.Join(paths.SourceDirectory, filename), entry.Value);
        if (DafnyOptions.O.CompileVerbose) {
          outputWriter.WriteLine("Additional target code written to {0}", Path.Join(paths.RelativeDirectory, filename));
        }
      }
    }

    static void WriteFile(string filename, string text, string moreText = null) {
      var dir = Path.GetDirectoryName(filename);
      if (dir != "") {
        Directory.CreateDirectory(dir);
      }

      using (TextWriter target = new StreamWriter(new FileStream(filename, System.IO.FileMode.Create))) {
        target.Write(text);
        if (moreText != null) {
          target.Write(moreText);
        }
      }
    }

    /// <summary>
    /// Generate a C# program from the Dafny program and, if "invokeCompiler" is "true", invoke
    /// the C# compiler to compile it.
    /// </summary>
    public static bool CompileDafnyProgram(Dafny.Program dafnyProgram, string dafnyProgramName,
                                           ReadOnlyCollection<string> otherFileNames, bool invokeCompiler,
                                           TextWriter outputWriter = null) {
      Contract.Requires(dafnyProgram != null);
      Contract.Assert(dafnyProgramName != null);

      if (outputWriter == null) {
        outputWriter = Console.Out;
      }

      // Compile the Dafny program into a string that contains the target program
      var oldErrorCount = dafnyProgram.reporter.Count(ErrorLevel.Error);
      Dafny.Compiler compiler;
      switch (DafnyOptions.O.CompileTarget) {
        case DafnyOptions.CompilationTarget.Csharp:
        default:
          compiler = new Dafny.CsharpCompiler(dafnyProgram.reporter);
          break;
        case DafnyOptions.CompilationTarget.JavaScript:
          compiler = new Dafny.JavaScriptCompiler(dafnyProgram.reporter);
          break;
        case DafnyOptions.CompilationTarget.Go:
          compiler = new Dafny.GoCompiler(dafnyProgram.reporter);
          break;
        case DafnyOptions.CompilationTarget.Java:
          compiler = new Dafny.JavaCompiler(dafnyProgram.reporter);
          break;
        case DafnyOptions.CompilationTarget.Cpp:
          compiler = new Dafny.CppCompiler(dafnyProgram.reporter, otherFileNames);
          break;
      }

      var hasMain = compiler.HasMain(dafnyProgram, out var mainMethod);
      if (hasMain) {
        mainMethod.IsEntryPoint = true;
        dafnyProgram.MainMethod = mainMethod;
      }
      string targetProgramText;
      var otherFiles = new Dictionary<string, string>();
      {
        var output = new ConcreteSyntaxTree();
        compiler.Compile(dafnyProgram, output);
        var writerOptions = new WriterState();
        var targetProgramTextWriter = new StringWriter();
        var files = new Queue<FileSyntax>();
        output.Render(targetProgramTextWriter, 0, writerOptions, files);
        targetProgramText = targetProgramTextWriter.ToString();

        while (files.Count > 0) {
          var file = files.Dequeue();
          var otherFileWriter = new StringWriter();
          writerOptions.HasNewLine = false;
          file.Tree.Render(otherFileWriter, 0, writerOptions, files);
          otherFiles.Add(file.Filename, otherFileWriter.ToString());
        }
      }
      string callToMain = null;
      if (hasMain) {
        var callToMainTree = new ConcreteSyntaxTree();
        string baseName = Path.GetFileNameWithoutExtension(dafnyProgramName);
        compiler.EmitCallToMain(mainMethod, baseName, callToMainTree);
        callToMain = callToMainTree.ToString(); // assume there aren't multiple files just to call main
      }
      Contract.Assert(hasMain == (callToMain != null));
      bool targetProgramHasErrors = dafnyProgram.reporter.Count(ErrorLevel.Error) != oldErrorCount;

      compiler.Coverage.WriteLegendFile();

      // blurt out the code to a file, if requested, or if other target-language files were specified on the command line.
      var paths = GenerateTargetPaths(compiler, dafnyProgramName);
      if (DafnyOptions.O.SpillTargetCode > 0 || otherFileNames.Count > 0 || (invokeCompiler && !compiler.SupportsInMemoryCompilation) ||
          (invokeCompiler && compiler.TextualTargetIsExecutable && !DafnyOptions.O.RunAfterCompile)) {
        WriteDafnyProgramToFiles(paths, targetProgramHasErrors, targetProgramText, callToMain, otherFiles, outputWriter);
      }

      if (targetProgramHasErrors) {
        return false;
      }
      // If we got here, compilation succeeded
      if (!invokeCompiler) {
        return true; // If we're not asked to invoke the target compiler, we can report success
      }

      // compile the program into an assembly
      var compiledCorrectly = compiler.CompileTargetProgram(dafnyProgramName, targetProgramText, callToMain, paths.Filename, otherFileNames,
        hasMain && DafnyOptions.O.RunAfterCompile, outputWriter, out var compilationResult);
      if (compiledCorrectly && DafnyOptions.O.RunAfterCompile) {
        if (hasMain) {
          if (DafnyOptions.O.CompileVerbose) {
            outputWriter.WriteLine("Running...");
            outputWriter.WriteLine();
          }
          compiledCorrectly = compiler.RunTargetProgram(dafnyProgramName, targetProgramText, callToMain, paths.Filename, otherFileNames, compilationResult, outputWriter);
        } else {
          // make sure to give some feedback to the user
          if (DafnyOptions.O.CompileVerbose) {
            outputWriter.WriteLine("Program compiled successfully");
          }
        }
      }
      return compiledCorrectly;
    }

    #endregion

  }
}
