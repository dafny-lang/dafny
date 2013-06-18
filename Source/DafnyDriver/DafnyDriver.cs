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
      if (CommandLineOptions.Clo.Files.Count == 0)
      {
        printer.ErrorWriteLine("*** Error: No input files were specified.");
        exitValue = ExitValue.PREPROCESSING_ERROR;
        goto END;
      }
      if (CommandLineOptions.Clo.XmlSink != null) {
        string errMsg = CommandLineOptions.Clo.XmlSink.Open();
        if (errMsg != null) {
          printer.ErrorWriteLine("*** Error: " + errMsg);
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
            printer.ErrorWriteLine("*** Error: '{0}': Filename extension '{1}' is not supported. Input files must be Dafny programs (.dfy).", file,
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
        return (int)exitValue;
    }


    static ExitValue ProcessFiles(List<string/*!*/>/*!*/ fileNames)
    {
      Contract.Requires(cce.NonNullElements(fileNames));
      ExitValue exitValue = ExitValue.VERIFIED;
      using (XmlFileScope xf = new XmlFileScope(CommandLineOptions.Clo.XmlSink, fileNames[fileNames.Count-1])) {
        Dafny.Program dafnyProgram;
        string programName = fileNames.Count == 1 ? fileNames[0] : "the program";
        string err = Dafny.Main.ParseCheck(fileNames, programName, out dafnyProgram);
        if (err != null) {
          exitValue = ExitValue.DAFNY_ERROR;
          printer.ErrorWriteLine(err);
        } else if (dafnyProgram != null && !CommandLineOptions.Clo.NoResolve && !CommandLineOptions.Clo.NoTypecheck) {
          Dafny.Translator translator = new Dafny.Translator();
          Bpl.Program boogieProgram = translator.Translate(dafnyProgram);
          if (CommandLineOptions.Clo.PrintFile != null)
          {
            ExecutionEngine.PrintBplFile(CommandLineOptions.Clo.PrintFile, boogieProgram, false, false);
          }

          string bplFilename;
          if (CommandLineOptions.Clo.PrintFile != null) {
            bplFilename = CommandLineOptions.Clo.PrintFile;
          } else {
            string baseName = cce.NonNull(Path.GetFileName(fileNames[fileNames.Count-1]));
            baseName = cce.NonNull(Path.ChangeExtension(baseName, "bpl"));
            bplFilename = Path.Combine(Path.GetTempPath(), baseName);
          }

          int errorCount, verified, inconclusives, timeOuts, outOfMemories;
          PipelineOutcome oc = BoogiePipelineWithRerun(boogieProgram, bplFilename, out errorCount, out verified, out inconclusives, out timeOuts, out outOfMemories);
          bool allOk = errorCount == 0 && inconclusives == 0 && timeOuts == 0 && outOfMemories == 0;
          switch (oc) {
            case PipelineOutcome.VerificationCompleted:
              printer.WriteTrailer(verified, errorCount, inconclusives, timeOuts, outOfMemories);
              if ((DafnyOptions.O.Compile && allOk && CommandLineOptions.Clo.ProcsToCheck == null) || DafnyOptions.O.ForceCompile)
                CompileDafnyProgram(dafnyProgram, fileNames[0]);
              break;
            case PipelineOutcome.Done:
              printer.WriteTrailer(verified, errorCount, inconclusives, timeOuts, outOfMemories);
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
        out int errorCount, out int verified, out int inconclusives, out int timeOuts, out int outOfMemories)
    {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out inconclusives) && 0 <= Contract.ValueAtReturn(out timeOuts));

      errorCount = verified = inconclusives = timeOuts = outOfMemories = 0;
      PipelineOutcome oc = ExecutionEngine.ResolveAndTypecheck(program, bplFileName);
      switch (oc) {
        case PipelineOutcome.Done:
          return oc;

        case PipelineOutcome.ResolutionError:
        case PipelineOutcome.TypeCheckingError:
          {
            ExecutionEngine.PrintBplFile(bplFileName, program, false, false);
            Console.WriteLine();
            Console.WriteLine("*** Encountered internal translation error - re-running Boogie to get better debug information");
            Console.WriteLine();

            List<string/*!*/>/*!*/ fileNames = new List<string/*!*/>();
            fileNames.Add(bplFileName);
            Bpl.Program reparsedProgram = ExecutionEngine.ParseBoogieProgram(fileNames, true);
            if (reparsedProgram != null) {
              ExecutionEngine.ResolveAndTypecheck(reparsedProgram, bplFileName);
            }
          }
          return oc;

        case PipelineOutcome.ResolvedAndTypeChecked:
          ExecutionEngine.EliminateDeadVariablesAndInline(program);
          return ExecutionEngine.InferAndVerify(program, out errorCount, out verified, out inconclusives, out timeOuts, out outOfMemories);

        default:
          Contract.Assert(false);throw new cce.UnreachableException();  // unexpected outcome
      }
    }


    #region Output

    static OutputPrinter printer;


    class DafnyConsolePrinter : ConsolePrinter
    {
      public override void ReportBplError(IToken tok, string message, bool error, bool showBplLocation, string category = null)
      {
        base.ReportBplError(tok, message, error, showBplLocation, category);

        if (tok is Dafny.NestedToken)
        {
          var nt = (Dafny.NestedToken)tok;
          ReportBplError(nt.Inner, "Related location", false, showBplLocation);
        }
      }
    }

    #endregion


    #region Compilation

    public static void CompileDafnyProgram(Dafny.Program dafnyProgram, string dafnyProgramName)
    {
      Contract.Requires(dafnyProgram != null);
      // Compile the Dafny program into a string that contains the C# program
      StringWriter sw = new StringWriter();
      Dafny.Compiler compiler = new Dafny.Compiler(sw);
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
            Console.WriteLine("Compiled program written to {0}", targetFilename);
          }
          else
          {
            Console.WriteLine("File {0} contains the partially compiled program", targetFilename);
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
        Console.WriteLine("Error: cannot compile, because there is no provider configured for input language CSharp");
      }
      else
      {
        var provider = CodeDomProvider.CreateProvider("CSharp");
        var cp = new System.CodeDom.Compiler.CompilerParameters();
        cp.GenerateExecutable = true;
        if (compiler.HasMain(dafnyProgram))
        {
          cp.OutputAssembly = Path.ChangeExtension(dafnyProgramName, "exe");
          cp.CompilerOptions = "/debug /nowarn:0164";  // warning CS0164 complains about unreferenced labels
        }
        else
        {
          cp.OutputAssembly = Path.ChangeExtension(dafnyProgramName, "dll");
          cp.CompilerOptions = "/debug /nowarn:0164 /target:library";  // warning CS0164 complains about unreferenced labels
        }
        cp.GenerateInMemory = false;
        cp.ReferencedAssemblies.Add("System.Numerics.dll");

        var cr = provider.CompileAssemblyFromSource(cp, csharpProgram);
        if (cr.Errors.Count == 0)
        {
          Console.WriteLine("Compiled assembly into {0}", cr.PathToAssembly);
        }
        else
        {
          Console.WriteLine("Errors compiling program into {0}", cr.PathToAssembly);
          foreach (var ce in cr.Errors)
          {
            Console.WriteLine(ce.ToString());
            Console.WriteLine();
          }
        }
      }
    }

    #endregion

  }
}
