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
  using System.CodeDom.Compiler;
  using System.Collections.Generic;
  using System.Collections.ObjectModel;
  using System.Diagnostics.Contracts;
  using System.IO;
  using System.Reflection;

  using Microsoft.Boogie;
  using Bpl = Microsoft.Boogie;

  public class DafnyDriver
  {
    enum ExitValue { VERIFIED = 0, PREPROCESSING_ERROR, DAFNY_ERROR, NOT_VERIFIED }


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

      ExitValue exitValue = ExitValue.VERIFIED;
      CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;
      if (!CommandLineOptions.Clo.Parse(args)) {
        exitValue = ExitValue.PREPROCESSING_ERROR;
        goto END;
      }
      //CommandLineOptions.Clo.Files = new List<string> { @"C:\dafny\Test\dafny0\Trait\TraitExtend.dfy" };

      if (CommandLineOptions.Clo.Files.Count == 0)
      {
        ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: No input files were specified.");
        exitValue = ExitValue.PREPROCESSING_ERROR;
        goto END;
      }
      if (CommandLineOptions.Clo.XmlSink != null) {
        string errMsg = CommandLineOptions.Clo.XmlSink.Open();
        if (errMsg != null) {
          ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: " + errMsg);
          exitValue = ExitValue.PREPROCESSING_ERROR;
          goto END;
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

      var dafnyFiles = new List<string>();
      var otherFiles = new List<string>();

      foreach (string file in CommandLineOptions.Clo.Files)
      { Contract.Assert(file != null);
        string extension = Path.GetExtension(file);
        if (extension != null) { extension = extension.ToLower(); }
        if (extension == ".dfy") {
          dafnyFiles.Add(file);
        }
        else if ((extension == ".cs") || (extension == ".dll")) {
          otherFiles.Add(file);
        }
        else {
          ExecutionEngine.printer.ErrorWriteLine(Console.Out, "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy) or C# files (.cs) or managed DLLS (.dll)", file,
            extension == null ? "" : extension);
          exitValue = ExitValue.PREPROCESSING_ERROR;
          goto END;
        }
      }
      exitValue = ProcessFiles(dafnyFiles, otherFiles.AsReadOnly(), reporter);

      END:
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


    static ExitValue ProcessFiles(IList<string/*!*/>/*!*/ dafnyFileNames, ReadOnlyCollection<string> otherFileNames, 
                                  ErrorReporter reporter, bool lookForSnapshots = true, string programId = null)
   {
      Contract.Requires(cce.NonNullElements(dafnyFileNames));

      if (programId == null)
      {
        programId = "main_program_id";
      }

      ExitValue exitValue = ExitValue.VERIFIED;
      if (CommandLineOptions.Clo.VerifySeparately && 1 < dafnyFileNames.Count)
      {
        foreach (var f in dafnyFileNames)
        {
          string extension = Path.GetExtension(f);
          if (extension != null) { extension = extension.ToLower(); }
          if (extension != ".dfy"){
            continue;
          }
          Console.WriteLine();
          Console.WriteLine("-------------------- {0} --------------------", f);
          var ev = ProcessFiles(new List<string> { f }, new List<string>().AsReadOnly(), reporter, lookForSnapshots, f);
          if (exitValue != ev && ev != ExitValue.VERIFIED)
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
          var ev = ProcessFiles(new List<string>(s), new List<string>().AsReadOnly(), reporter, false, programId);
          if (exitValue != ev && ev != ExitValue.VERIFIED)
          {
            exitValue = ev;
          }
        }
        return exitValue;
      }
      
      using (XmlFileScope xf = new XmlFileScope(CommandLineOptions.Clo.XmlSink, dafnyFileNames[dafnyFileNames.Count-1])) {
        Dafny.Program dafnyProgram;
        string programName = dafnyFileNames.Count == 1 ? dafnyFileNames[0] : "the program";
        string err = Dafny.Main.ParseCheck(dafnyFileNames, programName, reporter, out dafnyProgram);
        if (err != null) {
          exitValue = ExitValue.DAFNY_ERROR;
          ExecutionEngine.printer.ErrorWriteLine(Console.Out, err);
        } else if (dafnyProgram != null && !CommandLineOptions.Clo.NoResolve && !CommandLineOptions.Clo.NoTypecheck
            && DafnyOptions.O.DafnyVerify) {
          Dafny.Translator translator = new Dafny.Translator(dafnyProgram.reporter);
          Bpl.Program boogieProgram = translator.Translate(dafnyProgram);
          if (CommandLineOptions.Clo.PrintFile != null)
          {
            ExecutionEngine.PrintBplFile(CommandLineOptions.Clo.PrintFile, boogieProgram, false, false, CommandLineOptions.Clo.PrettyPrint);
          }

          string bplFilename;
          if (CommandLineOptions.Clo.PrintFile != null) {
            bplFilename = CommandLineOptions.Clo.PrintFile;
          } else {
            string baseName = cce.NonNull(Path.GetFileName(dafnyFileNames[dafnyFileNames.Count-1]));
            baseName = cce.NonNull(Path.ChangeExtension(baseName, "bpl"));
            bplFilename = Path.Combine(Path.GetTempPath(), baseName);
          }

          PipelineStatistics stats = null;
          PipelineOutcome oc = BoogiePipelineWithRerun(boogieProgram, bplFilename, out stats, 1 < Dafny.DafnyOptions.Clo.VerifySnapshots ? programId : null);
          var allOk = stats.ErrorCount == 0 && stats.InconclusiveCount == 0 && stats.TimeoutCount == 0 && stats.OutOfMemoryCount == 0;
          var resultFileName = DafnyOptions.O.DafnyPrintCompiledFile ?? dafnyFileNames[0];
          switch (oc) {
            case PipelineOutcome.VerificationCompleted:
              ExecutionEngine.printer.WriteTrailer(stats);
              if ((DafnyOptions.O.Compile && allOk && CommandLineOptions.Clo.ProcsToCheck == null) || DafnyOptions.O.ForceCompile)
                CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames);
              break;
            case PipelineOutcome.Done:
              ExecutionEngine.printer.WriteTrailer(stats);
              if (DafnyOptions.O.ForceCompile)
                CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames);
              break;
            default:
              // error has already been reported to user
              break;
          }
          exitValue = allOk ? ExitValue.VERIFIED : ExitValue.NOT_VERIFIED;
        }

        if (err == null && dafnyProgram != null && DafnyOptions.O.PrintStats) {
          Util.PrintStats(dafnyProgram);
        }
        if (err == null && dafnyProgram != null && DafnyOptions.O.PrintFunctionCallGraph) {
          Util.PrintFunctionCallGraph(dafnyProgram);
        }
      }
      return exitValue;
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

    static string WriteDafnyProgramToFile(string dafnyProgramName, string csharpProgram, bool completeProgram, TextWriter outputWriter)
    {
      string targetFilename = Path.ChangeExtension(dafnyProgramName, "cs");
      using (TextWriter target = new StreamWriter(new FileStream(targetFilename, System.IO.FileMode.Create))) {
        target.Write(csharpProgram);
        string relativeTarget = Path.GetFileName(targetFilename);
        if (completeProgram) {
          outputWriter.WriteLine("Compiled program written to {0}", relativeTarget);
        }
        else {
          outputWriter.WriteLine("File {0} contains the partially compiled program", relativeTarget);
        }
      }
      return targetFilename;
    }

    public static void CompileDafnyProgram(Dafny.Program dafnyProgram, string dafnyProgramName,
                                           ReadOnlyCollection<string> otherFileNames, TextWriter outputWriter = null)
    {
      Contract.Requires(dafnyProgram != null);

      if (outputWriter == null)
      {
        outputWriter = Console.Out;
      }

      // Compile the Dafny program into a string that contains the C# program
      StringWriter sw = new StringWriter();
      Dafny.Compiler compiler = new Dafny.Compiler();
      compiler.ErrorWriter = outputWriter;
      var hasMain = compiler.HasMain(dafnyProgram);
      if (DafnyOptions.O.RunAfterCompile && !hasMain) {
        // do no more
        return;
      }
      compiler.Compile(dafnyProgram, sw);
      var csharpProgram = sw.ToString();
      bool completeProgram = compiler.ErrorCount == 0;

      // blurt out the code to a file, if requested, or if other files were specified for the C# command line.
      string targetFilename = null;
      if (DafnyOptions.O.SpillTargetCode || (otherFileNames.Count > 0))
      {
        targetFilename = WriteDafnyProgramToFile(dafnyProgramName, csharpProgram, completeProgram, outputWriter);
      }

      // compile the program into an assembly
      if (!completeProgram)
      {
        // don't compile
      }
      else if (!CodeDomProvider.IsDefinedLanguage("CSharp"))
      {
        outputWriter.WriteLine("Error: cannot compile, because there is no provider configured for input language CSharp");
      }
      else
      {
        var provider = CodeDomProvider.CreateProvider("CSharp", new Dictionary<string, string> { { "CompilerVersion", "v4.0" } });
        var cp = new System.CodeDom.Compiler.CompilerParameters();
        cp.GenerateExecutable = hasMain;
        if (DafnyOptions.O.RunAfterCompile) {
          cp.GenerateInMemory = true;
        } else if (hasMain) {
          cp.OutputAssembly = Path.ChangeExtension(dafnyProgramName, "exe");
          cp.GenerateInMemory = false;
        } else {
          cp.OutputAssembly = Path.ChangeExtension(dafnyProgramName, "dll");
          cp.GenerateInMemory = false;
        }
        cp.CompilerOptions = "/debug /nowarn:0164 /nowarn:0219";  // warning CS0164 complains about unreferenced labels, CS0219 is about unused variables
        cp.ReferencedAssemblies.Add("System.Numerics.dll");
        cp.ReferencedAssemblies.Add("System.Core.dll");
        cp.ReferencedAssemblies.Add("System.dll");

        var libPath = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location) + Path.DirectorySeparatorChar;
        cp.ReferencedAssemblies.Add(libPath + "DafnyRuntime.dll");

        var immutableDllFileName = "System.Collections.Immutable.dll";
        var immutableDllPath = libPath + immutableDllFileName;

        if (DafnyOptions.O.Optimize) {
          cp.CompilerOptions += " /optimize /define:DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE";
          cp.ReferencedAssemblies.Add(immutableDllPath);
          cp.ReferencedAssemblies.Add("System.Runtime.dll");
        }

        int numOtherSourceFiles = 0;
        if (otherFileNames.Count > 0) {
          foreach (var file in otherFileNames) {
            string extension = Path.GetExtension(file);
            if (extension != null) { extension = extension.ToLower(); }
            if (extension == ".cs") {
              numOtherSourceFiles++;
            }
            else if (extension == ".dll") {
              cp.ReferencedAssemblies.Add(file);
            }
          }
        }

        CompilerResults cr;
        if (numOtherSourceFiles > 0) {
          string[] sourceFiles = new string[numOtherSourceFiles + 1];
          sourceFiles[0] = targetFilename;
          int index = 1;
          foreach (var file in otherFileNames) {
            string extension = Path.GetExtension(file);
            if (extension != null) { extension = extension.ToLower(); }
            if (extension == ".cs") {
              sourceFiles[index++] = file;
            }
          }
          cr = provider.CompileAssemblyFromFile(cp, sourceFiles);
        }
        else {
          cr = provider.CompileAssemblyFromSource(cp, csharpProgram);
        }
        var assemblyName = Path.GetFileName(cr.PathToAssembly);
        if (DafnyOptions.O.RunAfterCompile && cr.Errors.Count == 0) {
          outputWriter.WriteLine("Program compiled successfully");
          outputWriter.WriteLine("Running...");
          outputWriter.WriteLine();
          var entry = cr.CompiledAssembly.EntryPoint;
          try {
            object[] parameters = entry.GetParameters().Length == 0 ? new object[] { } : new object[] { new string[0] };
            entry.Invoke(null, parameters);
          } catch (System.Reflection.TargetInvocationException e) {
            outputWriter.WriteLine("Error: Execution resulted in exception: {0}", e.Message);
            outputWriter.WriteLine(e.InnerException.ToString());
          } catch (Exception e) {
            outputWriter.WriteLine("Error: Execution resulted in exception: {0}", e.Message);
            outputWriter.WriteLine(e.ToString());
          }
        } else if (cr.Errors.Count == 0) {
          outputWriter.WriteLine("Compiled assembly into {0}", assemblyName);
          if (DafnyOptions.O.Optimize) {
            var outputDir = Path.GetDirectoryName(dafnyProgramName);
            if (string.IsNullOrWhiteSpace(outputDir)) {
              outputDir = ".";
            }
            var destPath = outputDir + Path.DirectorySeparatorChar + immutableDllFileName;
            File.Copy(immutableDllPath, destPath, true);
            outputWriter.WriteLine("Copied /optimize dependency {0} to {1}", immutableDllFileName, outputDir);
          }
        } else {
          outputWriter.WriteLine("Errors compiling program into {0}", assemblyName);
          foreach (var ce in cr.Errors) {
            outputWriter.WriteLine(ce.ToString());
            outputWriter.WriteLine();
          }
        }
      }
    }

    #endregion

  }
}
