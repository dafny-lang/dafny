//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// DafnyDriver
//       - main program for taking a Dafny program and verifying it
//---------------------------------------------------------------------------------------------

namespace Microsoft.Dafny
{
  using System;
  using System.Collections.Generic;
  using System.Collections.ObjectModel;
  using System.Diagnostics.Contracts;
  using System.IO;
  using System.Linq;

  using Microsoft.Boogie;
  using Bpl = Microsoft.Boogie;
  using System.Diagnostics;

  public class DafnyDriver
  {
    // TODO: Refactor so that non-errors (NOT_VERIFIED, DONT_PROCESS_FILES) don't result in non-zero exit codes
    public enum ExitValue { SUCCESS = 0, PREPROCESSING_ERROR, DAFNY_ERROR, COMPILE_ERROR, VERIFICATION_ERROR }

    public static int Main(string[] args)
    {
      int ret = 0;
      var thread = new System.Threading.Thread(
        new System.Threading.ThreadStart(() =>
          { ret = ThreadMain(args); }),
          0x10000000); // 256MB stack size to prevent stack overflow
      thread.Start();
      thread.Join();
      return ret;
    }

    public static int ThreadMain(string[] args)
    {
      Contract.Requires(cce.NonNullElements(args));

      ErrorReporter reporter = new ConsoleErrorReporter();
      ExecutionEngine.printer = new DafnyConsolePrinter(); // For boogie errors

      DafnyOptions.Install(new DafnyOptions(reporter));

      List<DafnyFile> dafnyFiles;
      List<string> otherFiles;

      CommandLineArgumentsResult cliArgumentsResult = ProcessCommandLineArguments(args, out dafnyFiles, out otherFiles);
      ExitValue exitValue;
      switch (cliArgumentsResult)
      {
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
      }
      if (CommandLineOptions.Clo.Wait)
      {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }
      if (!DafnyOptions.O.CountVerificationErrors && exitValue != ExitValue.PREPROCESSING_ERROR)
      {
        return 0;
      }
      //Console.ReadKey();
      return (int)exitValue;
    }

    public enum CommandLineArgumentsResult
    {
      /// Indicates that arguments were parsed successfully.
      OK,
      /// Indicates that arguments were not parsed successfully.
      PREPROCESSING_ERROR,
      /// Indicates that arguments were parsed successfully, but the program should exit without processing files.
      OK_EXIT_EARLY
    }

    public static CommandLineArgumentsResult ProcessCommandLineArguments(string[] args, out List<DafnyFile> dafnyFiles, out List<string> otherFiles)
    {
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

      if (DafnyOptions.O.PrintVersionAndExit)
      {
        Console.WriteLine(CommandLineOptions.Clo.Version);
        return CommandLineArgumentsResult.OK_EXIT_EARLY;
      }

      if (CommandLineOptions.Clo.HelpRequested)
      {
        return CommandLineArgumentsResult.OK_EXIT_EARLY;
      }

      if (CommandLineOptions.Clo.Files.Count == 0)
      {
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
      if (!CommandLineOptions.Clo.DontShowLogo)
      {
        Console.WriteLine(CommandLineOptions.Clo.Version);
      }
      if (CommandLineOptions.Clo.ShowEnv == CommandLineOptions.ShowEnvironment.Always)
      {
        Console.WriteLine("---Command arguments");
        foreach (string arg in args)
        {Contract.Assert(arg != null);
          Console.WriteLine(arg);
        }
        Console.WriteLine("--------------------");
      }

      foreach (string file in CommandLineOptions.Clo.Files)
      { Contract.Assert(file != null);
        string extension = Path.GetExtension(file);
        if (extension != null) { extension = extension.ToLower(); }

        bool isDafnyFile = false;
        try {
          dafnyFiles.Add(new DafnyFile(file));
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
      if (dafnyFiles.Count == 0) { ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files");
        return CommandLineArgumentsResult.PREPROCESSING_ERROR;
      }
      return CommandLineArgumentsResult.OK;
    }

    static ExitValue ProcessFiles(IList<DafnyFile/*!*/>/*!*/ dafnyFiles, ReadOnlyCollection<string> otherFileNames,
                                  ErrorReporter reporter, bool lookForSnapshots = true, string programId = null)
   {
      Contract.Requires(cce.NonNullElements(dafnyFiles));
      var dafnyFileNames = DafnyFile.fileNames(dafnyFiles);

      ExitValue exitValue = ExitValue.SUCCESS;
      if (CommandLineOptions.Clo.VerifySeparately && 1 < dafnyFiles.Count)
      {
        foreach (var f in dafnyFiles)
        {
          Console.WriteLine();
          Console.WriteLine("-------------------- {0} --------------------", f);
          var ev = ProcessFiles(new List<DafnyFile> { f }, new List<string>().AsReadOnly(), reporter, lookForSnapshots, f.FilePath);
          if (exitValue != ev && ev != ExitValue.SUCCESS)
          {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      if (0 <= CommandLineOptions.Clo.VerifySnapshots && lookForSnapshots)
      {
        var snapshotsByVersion = ExecutionEngine.LookForSnapshots(dafnyFileNames);
        foreach (var s in snapshotsByVersion)
        {
          var snapshots = new List<DafnyFile>();
          foreach (var f in s) {
            snapshots.Add(new DafnyFile(f));
          }
          var ev = ProcessFiles(snapshots, new List<string>().AsReadOnly(), reporter, false, programId);
          if (exitValue != ev && ev != ExitValue.SUCCESS)
          {
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
      return exitValue;
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
                              out PipelineStatistics stats, out PipelineOutcome oc)
    {
      if (programId == null)
      {
        programId = "main_program_id";
      }
      programId += "_" + moduleName;

      string bplFilename;
      if (CommandLineOptions.Clo.PrintFile != null)
      {
        bplFilename = CommandLineOptions.Clo.PrintFile;
      }
      else
      {
        string baseName = cce.NonNull(Path.GetFileName(baseFile));
        baseName = cce.NonNull(Path.ChangeExtension(baseName, "bpl"));
        bplFilename = Path.Combine(Path.GetTempPath(), baseName);
      }

      bplFilename = BoogieProgramSuffix(bplFilename, moduleName);
      stats = null;
      oc = BoogiePipelineWithRerun(boogieProgram, bplFilename, out stats, 1 < Dafny.DafnyOptions.Clo.VerifySnapshots ? programId : null);
      return (oc == PipelineOutcome.Done || oc == PipelineOutcome.VerificationCompleted) && stats.ErrorCount == 0 && stats.InconclusiveCount == 0 && stats.TimeoutCount == 0 && stats.OutOfMemoryCount == 0;
    }

    public static bool Boogie(string baseName, IEnumerable<Tuple<string, Bpl.Program>> boogiePrograms, string programId, out Dictionary<string, PipelineStatistics> statss, out PipelineOutcome oc) {

      bool isVerified = true;
      oc = PipelineOutcome.VerificationCompleted;
      statss = new Dictionary<string, PipelineStatistics>();

      Stopwatch watch = new Stopwatch();
      watch.Start();

      foreach (var prog in boogiePrograms) {
        PipelineStatistics newstats;
        PipelineOutcome newoc;

        if (DafnyOptions.O.SeparateModuleOutput) {
          ExecutionEngine.printer.AdvisoryWriteLine("For module: {0}", prog.Item1);
        }

        isVerified = BoogieOnce(baseName, prog.Item1, prog.Item2, programId, out newstats, out newoc) && isVerified;

        watch.Stop();

        if ((oc == PipelineOutcome.VerificationCompleted || oc == PipelineOutcome.Done) && newoc != PipelineOutcome.VerificationCompleted) {
          oc = newoc;
        }

        if (DafnyOptions.O.SeparateModuleOutput) {
          TimeSpan ts = watch.Elapsed;
          string elapsedTime = String.Format("{0:00}:{1:00}:{2:00}",
            ts.Hours, ts.Minutes, ts.Seconds);
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
      if (CommandLineOptions.Clo.vcVariety != CommandLineOptions.VCVariety.Doomed && !CommandLineOptions.Clo.Verify && stats.ErrorCount == 0) {
        Console.WriteLine();
        Console.Write("{0} did not attempt verification", CommandLineOptions.Clo.DescriptiveToolName);
        if (stats.InconclusiveCount != 0) {
          Console.Write(", {0} inconclusive{1}", stats.InconclusiveCount, stats.InconclusiveCount == 1 ? "" : "s");
        }
        if (stats.TimeoutCount != 0) {
          Console.Write(", {0} time out{1}", stats.TimeoutCount, stats.TimeoutCount == 1 ? "" : "s");
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
        statSum.OutOfMemoryCount += stats.Value.OutOfMemoryCount;
        statSum.CachedErrorCount += stats.Value.CachedErrorCount;
        statSum.CachedInconclusiveCount += stats.Value.CachedInconclusiveCount;
        statSum.CachedOutOfMemoryCount += stats.Value.CachedOutOfMemoryCount;
        statSum.CachedTimeoutCount += stats.Value.CachedTimeoutCount;
        statSum.CachedVerifiedCount += stats.Value.CachedVerifiedCount;
        statSum.InconclusiveCount += stats.Value.InconclusiveCount;
      }
      WriteTrailer(statSum);
    }


    public static bool Compile(string fileName, ReadOnlyCollection<string> otherFileNames, Program dafnyProgram,
                               PipelineOutcome oc, Dictionary<string, PipelineStatistics> statss, bool verified)
    {
      var resultFileName = DafnyOptions.O.DafnyPrintCompiledFile ?? fileName;
      bool compiled = true;
      switch (oc)
      {
        case PipelineOutcome.VerificationCompleted:
          WriteStatss(statss);
          if ((DafnyOptions.O.Compile && verified && CommandLineOptions.Clo.ProcsToCheck == null) || DafnyOptions.O.ForceCompile) {
            compiled = CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, true);
          } else if ((2 <= DafnyOptions.O.SpillTargetCode && verified && CommandLineOptions.Clo.ProcsToCheck == null) || 3 <= DafnyOptions.O.SpillTargetCode) {
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
        out PipelineStatistics stats, string programId)
    {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out stats).InconclusiveCount && 0 <= Contract.ValueAtReturn(out stats).TimeoutCount);

      stats = new PipelineStatistics();
      LinearTypeChecker ltc;
      CivlTypeChecker ctc;
      PipelineOutcome oc = ExecutionEngine.ResolveAndTypecheck(program, bplFileName, out ltc, out ctc);
      switch (oc) {
        case PipelineOutcome.Done:
          return oc;

        case PipelineOutcome.ResolutionError:
        case PipelineOutcome.TypeCheckingError:
          {
            ExecutionEngine.PrintBplFile(bplFileName, program, false, false, CommandLineOptions.Clo.PrettyPrint);
            Console.WriteLine();
            Console.WriteLine("*** Encountered internal translation error - re-running Boogie to get better debug information");
            Console.WriteLine();

            List<string/*!*/>/*!*/ fileNames = new List<string/*!*/>();
            fileNames.Add(bplFileName);
            Bpl.Program reparsedProgram = ExecutionEngine.ParseBoogieProgram(fileNames, true);
            if (reparsedProgram != null) {
              ExecutionEngine.ResolveAndTypecheck(reparsedProgram, bplFileName, out ltc, out ctc);
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

    class DafnyConsolePrinter : ConsolePrinter
    {
      public override void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null)
      {
        // Dafny has 0-indexed columns, but Boogie counts from 1
        var realigned_tok = new Token(tok.line, tok.col - 1);
        realigned_tok.kind = tok.kind;
        realigned_tok.pos = tok.pos;
        realigned_tok.val = tok.val;
        realigned_tok.filename = tok.filename;
        base.ReportBplError(realigned_tok, message, error, tw, category);

        if (tok is Dafny.NestedToken)
        {
          var nt = (Dafny.NestedToken)tok;
          ReportBplError(nt.Inner, "Related location", false, tw);
        }
      }
    }

    #endregion


    #region Compilation

    static string WriteDafnyProgramToFiles(Compiler compiler, string dafnyProgramName, string targetProgram, bool completeProgram, Dictionary<String, String> otherFiles, TextWriter outputWriter)
    {
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
          targetBaseDir = baseName;
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
      // WARNING: Make sure that Directory.Delete is only called when the compilation target is Java.
      // If called during C# or JS compilation, you will lose your entire target directory.
      // Purpose is to delete the old generated folder with the Java compilation output and replace all contents.
      if (DafnyOptions.O.CompileTarget is DafnyOptions.CompilationTarget.Java && Directory.Exists(targetDir))
        Directory.Delete(targetDir, true);
      string targetFilename = Path.Combine(targetDir, targetBaseName);
      if (targetProgram != null) {
        WriteFile(targetFilename, targetProgram);
      }

      string relativeTarget = Path.Combine(targetBaseDir, targetBaseName);
      if (completeProgram && targetProgram != null) {
        if (DafnyOptions.O.CompileVerbose) {
          outputWriter.WriteLine("Compiled program written to {0}", relativeTarget);
        }
      }
      else {
        outputWriter.WriteLine("File {0} contains the partially compiled program", relativeTarget);
      }

      foreach (var entry in otherFiles) {
        var filename = entry.Key;
        WriteFile(Path.Combine(targetDir, filename), entry.Value);
        if (DafnyOptions.O.CompileVerbose) {
          outputWriter.WriteLine("Additional code written to {0}", Path.Combine(targetBaseDir, filename));
        }
      }
      return targetFilename;
    }

    static void WriteFile(string filename, string text) {
      var dir = Path.GetDirectoryName(filename);
      if (dir != "") {
        Directory.CreateDirectory(dir);
      }

      using (TextWriter target = new StreamWriter(new FileStream(filename, System.IO.FileMode.Create))) {
        target.Write(text);
      }
    }

    /// <summary>
    /// Generate a C# program from the Dafny program and, if "invokeCompiler" is "true", invoke
    /// the C# compiler to compile it.
    /// </summary>
    public static bool CompileDafnyProgram(Dafny.Program dafnyProgram, string dafnyProgramName,
                                           ReadOnlyCollection<string> otherFileNames, bool invokeCompiler,
                                           TextWriter outputWriter = null)
    {
      Contract.Requires(dafnyProgram != null);
      Contract.Assert(dafnyProgramName != null);

      if (outputWriter == null)
      {
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

      Method mainMethod;
      var hasMain = compiler.HasMain(dafnyProgram, out mainMethod);
      string targetProgramText;
      var otherFiles = new Dictionary<string, string>();
      {
        var fileQueue = new Queue<FileTargetWriter>();
        using (var wr = new TargetWriter(0)) {
          compiler.Compile(dafnyProgram, wr);
          var sw = new StringWriter();
          wr.Collect(sw, fileQueue);
          targetProgramText = sw.ToString();
        }

        while (fileQueue.Count > 0) {
          var wr = fileQueue.Dequeue();
          var sw = new StringWriter();
          wr.Collect(sw, fileQueue);
          otherFiles.Add(wr.Filename, sw.ToString());
        }
      }
      string baseName = Path.GetFileNameWithoutExtension(dafnyProgramName);
      string callToMain = null;
      if (hasMain) {
        using (var wr = new TargetWriter(0)) {
          if (DafnyOptions.O.CompileTarget is DafnyOptions.CompilationTarget.Java) {
            baseName = compiler.TransformToClassName(baseName);
            wr.WriteLine($"public class {baseName} {{");
          }
          compiler.EmitCallToMain(mainMethod, wr);
          if (DafnyOptions.O.CompileTarget is DafnyOptions.CompilationTarget.Java) {
            wr.WriteLine("}");
          }
          callToMain = wr.ToString(); // assume there aren't multiple files just to call main
        }
      }
      bool completeProgram = dafnyProgram.reporter.Count(ErrorLevel.Error) == oldErrorCount;

      compiler.Coverage.WriteLegendFile();

      // blurt out the code to a file, if requested, or if other files were specified for the C# command line.
      string targetFilename = null;
      if (DafnyOptions.O.SpillTargetCode > 0 || otherFileNames.Count > 0 || (invokeCompiler && !compiler.SupportsInMemoryCompilation))
      {
        var p = callToMain == null ? targetProgramText : targetProgramText + callToMain;
        if (DafnyOptions.O.CompileTarget is DafnyOptions.CompilationTarget.Java && callToMain == null) {
          p = null;
        }
        targetFilename = WriteDafnyProgramToFiles(compiler, dafnyProgramName, p, completeProgram, otherFiles, outputWriter);
      }

      if (DafnyOptions.O.CompileTarget is DafnyOptions.CompilationTarget.Java) {
        string targetBaseDir = Path.GetFileNameWithoutExtension(dafnyProgramName);
        string targetDir = Path.Combine(Path.GetDirectoryName(dafnyProgramName), targetBaseDir);
        var assemblyLocation = System.Reflection.Assembly.GetExecutingAssembly().Location;
        Contract.Assert(assemblyLocation != null);
        var codebase = System.IO.Path.GetDirectoryName(assemblyLocation);
        Contract.Assert(codebase != null);
        string dest = targetDir + "/dafny";
        Directory.CreateDirectory(dest);
        var jcompiler = (JavaCompiler) compiler;
        jcompiler.CompileTuples(dest);
        jcompiler.CreateFunctionInterface(dest);
        jcompiler.CompileDafnyArrays(dest);
      }

      if (!completeProgram) {
        return false;
      }
      // If we got until here, compilation to C# succeeded
      if (!invokeCompiler) {
        return true; // If we're not asked to invoke the C# to assembly compiler, we can report success
      }

      // compile the program into an assembly
      object compilationResult;
      var compiledCorrectly = compiler.CompileTargetProgram(dafnyProgramName, targetProgramText, callToMain, targetFilename, otherFileNames,
        hasMain, hasMain && DafnyOptions.O.RunAfterCompile, outputWriter, out compilationResult);
      if (compiledCorrectly && DafnyOptions.O.RunAfterCompile) {
        if (hasMain) {
          if (DafnyOptions.O.CompileVerbose) {
            outputWriter.WriteLine("Running...");
            outputWriter.WriteLine();
          }
          compiledCorrectly = compiler.RunTargetProgram(dafnyProgramName, targetProgramText, callToMain, targetFilename, otherFileNames, compilationResult, outputWriter);
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
