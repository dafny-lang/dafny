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
  using System.Diagnostics.Contracts;
  using System.IO;
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
         
      printer = new DafnyConsolePrinter();
      ExecutionEngine.printer = printer;

      DafnyOptions.Install(new DafnyOptions());

      ExitValue exitValue = ExitValue.VERIFIED;
      CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;
      if (!CommandLineOptions.Clo.Parse(args)) {
        exitValue = ExitValue.PREPROCESSING_ERROR;
        goto END;
      }
      //CommandLineOptions.Clo.Files = new List<string> { @"C:\dafny\Test\dafny0\Trait\TraitExtend.dfy" };

      if (CommandLineOptions.Clo.Files.Count == 0)
      {
        printer.ErrorWriteLine(Console.Out, "*** Error: No input files were specified.");
        exitValue = ExitValue.PREPROCESSING_ERROR;
        goto END;
      }
      if (CommandLineOptions.Clo.XmlSink != null) {
        string errMsg = CommandLineOptions.Clo.XmlSink.Open();
        if (errMsg != null) {
          printer.ErrorWriteLine(Console.Out, "*** Error: " + errMsg);
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

      foreach (string file in CommandLineOptions.Clo.Files)
      {Contract.Assert(file != null);
        string extension = Path.GetExtension(file);
        if (extension != null) { extension = extension.ToLower(); }
        if (extension != ".dfy")
        {
            printer.ErrorWriteLine(Console.Out, "*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy).", file,
                extension == null ? "" : extension);
            exitValue = ExitValue.PREPROCESSING_ERROR;
            goto END;
        }
      }
      exitValue = ProcessFiles(CommandLineOptions.Clo.Files);

      END:
        if (CommandLineOptions.Clo.XmlSink != null) {
          CommandLineOptions.Clo.XmlSink.Close();
        }
        if (CommandLineOptions.Clo.Wait)
        {
          Console.WriteLine("Press Enter to exit.");
          Console.ReadLine();
        }
        if (CommandLineOptions.Clo.UseBaseNameForFileName && exitValue != ExitValue.PREPROCESSING_ERROR)
        {
          // TODO(wuestholz): We should probably add a separate flag for this. This is currently only used by the new testing infrastructure.
          return 0;
        }
        //Console.ReadKey();
        return (int)exitValue;
    }


    static ExitValue ProcessFiles(IList<string/*!*/>/*!*/ fileNames, bool lookForSnapshots = true, string programId = null)
    {
      Contract.Requires(cce.NonNullElements(fileNames));

      if (programId == null)
      {
        programId = "main_program_id";
      }

      ExitValue exitValue = ExitValue.VERIFIED;
      if (CommandLineOptions.Clo.VerifySeparately && 1 < fileNames.Count)
      {
        foreach (var f in fileNames)
        {
          Console.WriteLine();
          Console.WriteLine("-------------------- {0} --------------------", f);
          var ev = ProcessFiles(new List<string> { f }, lookForSnapshots, f);
          if (exitValue != ev && ev != ExitValue.VERIFIED)
          {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      if (0 <= CommandLineOptions.Clo.VerifySnapshots && lookForSnapshots)
      {
        var snapshotsByVersion = ExecutionEngine.LookForSnapshots(fileNames);
        foreach (var s in snapshotsByVersion)
        {
          var ev = ProcessFiles(new List<string>(s), false, programId);
          if (exitValue != ev && ev != ExitValue.VERIFIED)
          {
            exitValue = ev;
          }
        }
        return exitValue;
      }
      
      using (XmlFileScope xf = new XmlFileScope(CommandLineOptions.Clo.XmlSink, fileNames[fileNames.Count-1])) {
        Dafny.Program dafnyProgram;
        string programName = fileNames.Count == 1 ? fileNames[0] : "the program";
        string err = Dafny.Main.ParseCheck(fileNames, programName, out dafnyProgram);
        if (err != null) {
          exitValue = ExitValue.DAFNY_ERROR;
          printer.ErrorWriteLine(Console.Out, err);
        } else if (dafnyProgram != null && !CommandLineOptions.Clo.NoResolve && !CommandLineOptions.Clo.NoTypecheck
            && DafnyOptions.O.DafnyVerify) {
          Dafny.Translator translator = new Dafny.Translator();
          Bpl.Program boogieProgram = translator.Translate(dafnyProgram);
          if (CommandLineOptions.Clo.PrintFile != null)
          {
            ExecutionEngine.PrintBplFile(CommandLineOptions.Clo.PrintFile, boogieProgram, false, false, CommandLineOptions.Clo.PrettyPrint);
          }

          string bplFilename;
          if (CommandLineOptions.Clo.PrintFile != null) {
            bplFilename = CommandLineOptions.Clo.PrintFile;
          } else {
            string baseName = cce.NonNull(Path.GetFileName(fileNames[fileNames.Count-1]));
            baseName = cce.NonNull(Path.ChangeExtension(baseName, "bpl"));
            bplFilename = Path.Combine(Path.GetTempPath(), baseName);
          }

          PipelineStatistics stats = null;
          PipelineOutcome oc = BoogiePipelineWithRerun(boogieProgram, bplFilename, out stats, 1 < Dafny.DafnyOptions.Clo.VerifySnapshots ? programId : null);
          var allOk = stats.ErrorCount == 0 && stats.InconclusiveCount == 0 && stats.TimeoutCount == 0 && stats.OutOfMemoryCount == 0;
          switch (oc) {
            case PipelineOutcome.VerificationCompleted:
              printer.WriteTrailer(stats);
              if ((DafnyOptions.O.Compile && allOk && CommandLineOptions.Clo.ProcsToCheck == null) || DafnyOptions.O.ForceCompile)
                CompileDafnyProgram(dafnyProgram, fileNames[0]);
              break;
            case PipelineOutcome.Done:
              printer.WriteTrailer(stats);
              if (DafnyOptions.O.ForceCompile)
                CompileDafnyProgram(dafnyProgram, fileNames[0]);
              break;
            default:
              // error has already been reported to user
              break;
          }
          exitValue = allOk ? ExitValue.VERIFIED : ExitValue.NOT_VERIFIED;
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
      MoverTypeChecker mtc;
      PipelineOutcome oc = ExecutionEngine.ResolveAndTypecheck(program, bplFileName, out ltc, out mtc);
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
              ExecutionEngine.ResolveAndTypecheck(reparsedProgram, bplFileName, out ltc, out mtc);
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

    static OutputPrinter printer;


    class DafnyConsolePrinter : ConsolePrinter
    {
      public override void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null)
      {
        base.ReportBplError(tok, message, error, tw, category);

        if (tok is Dafny.NestedToken)
        {
          var nt = (Dafny.NestedToken)tok;
          ReportBplError(nt.Inner, "Related location", false, tw);
        }
      }
    }

    #endregion


    #region Compilation

    public static void CompileDafnyProgram(Dafny.Program dafnyProgram, string dafnyProgramName, TextWriter outputWriter = null)
    {
      Contract.Requires(dafnyProgram != null);

      if (outputWriter == null)
      {
        outputWriter = Console.Out;
      }

      // Compile the Dafny program into a string that contains the C# program
      StringWriter sw = new StringWriter();
      Dafny.Compiler compiler = new Dafny.Compiler(sw);
      compiler.ErrorWriter = outputWriter;
      var hasMain = compiler.HasMain(dafnyProgram);
      if (DafnyOptions.O.RunAfterCompile && !hasMain) {
        // do no more
        return;
      }
      compiler.Compile(dafnyProgram);
      var csharpProgram = sw.ToString();
      bool completeProgram = compiler.ErrorCount == 0;

      // blurt out the code to a file
      if (DafnyOptions.O.SpillTargetCode)
      {
        string targetFilename = Path.ChangeExtension(dafnyProgramName, "cs");
        using (TextWriter target = new StreamWriter(new FileStream(targetFilename, System.IO.FileMode.Create)))
        {
          target.Write(csharpProgram);
          if (completeProgram)
          {
            outputWriter.WriteLine("Compiled program written to {0}", targetFilename);
          }
          else
          {
            outputWriter.WriteLine("File {0} contains the partially compiled program", targetFilename);
          }
        }
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
        var provider = CodeDomProvider.CreateProvider("CSharp");
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

        var cr = provider.CompileAssemblyFromSource(cp, csharpProgram);
        var assemblyName = Path.GetFileName(cr.PathToAssembly);
        if (DafnyOptions.O.RunAfterCompile && cr.Errors.Count == 0) {
          outputWriter.WriteLine("Program compiled successfully");
          outputWriter.WriteLine("Running...");
          outputWriter.WriteLine();
          var entry = cr.CompiledAssembly.EntryPoint;
          try {
            entry.Invoke(null, new object[] { new string[0] });
          } catch (System.Reflection.TargetInvocationException e) {
            outputWriter.WriteLine("Error: Execution resulted in exception: {0}", e.Message);
            outputWriter.WriteLine(e.InnerException.ToString());
          } catch (Exception e) {
            outputWriter.WriteLine("Error: Execution resulted in exception: {0}", e.Message);
            outputWriter.WriteLine(e.ToString());
          }
        } else if (cr.Errors.Count == 0) {
          outputWriter.WriteLine("Compiled assembly into {0}", assemblyName);
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
