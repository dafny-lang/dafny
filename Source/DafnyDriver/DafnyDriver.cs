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
  using VC;
  using Bpl = Microsoft.Boogie;

  public class DafnyDriver
  {

    enum ExitValue { VERIFIED = 0, PREPROCESSING_ERROR, DAFNY_ERROR, NOT_VERIFIED }

    public static int Main(string[] args)
    {
      Contract.Requires(cce.NonNullElements(args));

      DafnyOptions.Install(new DafnyOptions());

      //assert forall{int i in (0:args.Length); args[i] != null};
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
          return InferAndVerify(program, out errorCount, out verified, out inconclusives, out timeOuts, out outOfMemories);

        default:
          Contract.Assert(false);throw new cce.UnreachableException();  // unexpected outcome
      }
    }


    /// <summary>
    /// Given a resolved and type checked Boogie program, infers invariants for the program
    /// and then attempts to verify it.  Returns:
    ///  - Done if command line specified no verification
    ///  - FatalError if a fatal error occurred, in which case an error has been printed to console
    ///  - VerificationCompleted if inference and verification completed, in which the out
    ///    parameters contain meaningful values
    /// </summary>
    static PipelineOutcome InferAndVerify(Bpl.Program program,
                                          out int errorCount, out int verified, out int inconclusives, out int timeOuts, out int outOfMemories)
    {
      Contract.Requires(program != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out inconclusives) && 0 <= Contract.ValueAtReturn(out timeOuts));

      errorCount = verified = inconclusives = timeOuts = outOfMemories = 0;

      // ---------- Infer invariants --------------------------------------------------------

      // Abstract interpretation -> Always use (at least) intervals, if not specified otherwise (e.g. with the "/noinfer" switch)
      if (CommandLineOptions.Clo.UseAbstractInterpretation) {
        if (CommandLineOptions.Clo.Ai.J_Intervals || CommandLineOptions.Clo.Ai.J_Trivial) {
          Microsoft.Boogie.AbstractInterpretation.NativeAbstractInterpretation.RunAbstractInterpretation(program);
        } else {
          // use /infer:j as the default
          CommandLineOptions.Clo.Ai.J_Intervals = true;
          Microsoft.Boogie.AbstractInterpretation.NativeAbstractInterpretation.RunAbstractInterpretation(program);
        }
      }

      if (CommandLineOptions.Clo.LoopUnrollCount != -1) {
        program.UnrollLoops(CommandLineOptions.Clo.LoopUnrollCount, CommandLineOptions.Clo.SoundLoopUnrolling);
      }

      if (CommandLineOptions.Clo.PrintInstrumented) {
        program.Emit(new TokenTextWriter(Console.Out));
      }

      if (CommandLineOptions.Clo.ExpandLambdas) {
        LambdaHelper.ExpandLambdas(program);
      }

      // ---------- Verify ------------------------------------------------------------

      if (!CommandLineOptions.Clo.Verify) { return PipelineOutcome.Done; }

      #region Verify each implementation

#if ROB_DEBUG
      string now = DateTime.Now.ToString().Replace(' ','-').Replace('/','-').Replace(':','-');
      System.IO.StreamWriter w = new System.IO.StreamWriter(@"\temp\batch_"+now+".bpl");
      program.Emit(new TokenTextWriter(w));
      w.Close();
#endif

      ConditionGeneration vcgen = null;
      try
      {
        vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend);
      }
      catch (ProverException e)
      {
        printer.ErrorWriteLine("Fatal Error: ProverException: {0}", e);
        return PipelineOutcome.FatalError;
      }

      var decls = program.TopLevelDeclarations.ToArray();
      foreach (var decl in decls )
      {
        Contract.Assert(decl != null);
        Implementation impl = decl as Implementation;
        if (impl != null && CommandLineOptions.Clo.UserWantsToCheckRoutine(cce.NonNull(impl.Name)) && !impl.SkipVerification)
        {
            List<Counterexample>/*?*/ errors;

            DateTime start = new DateTime();  // to please compiler's definite assignment rules
            if (CommandLineOptions.Clo.Trace || CommandLineOptions.Clo.TraceProofObligations || CommandLineOptions.Clo.XmlSink != null)
            {
                start = DateTime.Now;
                if (CommandLineOptions.Clo.Trace || CommandLineOptions.Clo.TraceProofObligations)
                {
                    Console.WriteLine();
                    Console.WriteLine("Verifying {0} ...", impl.Name);
                }
                if (CommandLineOptions.Clo.XmlSink != null)
                {
                    CommandLineOptions.Clo.XmlSink.WriteStartMethod(impl.Name, start);
                }
            }

            ConditionGeneration.Outcome outcome;
            int prevAssertionCount = vcgen.CumulativeAssertionCount;
            try
            {
                outcome = vcgen.VerifyImplementation(impl, out errors);
            }
            catch (VCGenException e)
            {
                ReportBplError(impl.tok, String.Format("Error BP5010: {0}  Encountered in implementation {1}.", e.Message, impl.Name), true);
                errors = null;
                outcome = VCGen.Outcome.Inconclusive;
            }
            catch (UnexpectedProverOutputException upo)
            {
                printer.AdvisoryWriteLine("Advisory: {0} SKIPPED because of internal error: unexpected prover output: {1}", impl.Name, upo.Message);
                errors = null;
                outcome = VCGen.Outcome.Inconclusive;
            }

            string timeIndication = "";
            DateTime end = DateTime.Now;
            TimeSpan elapsed = end - start;
            if (CommandLineOptions.Clo.Trace) {
              int poCount = vcgen.CumulativeAssertionCount - prevAssertionCount;
              timeIndication = string.Format("  [{0:F3} s, {1} proof obligation{2}]  ", elapsed.TotalSeconds, poCount, poCount == 1 ? "" : "s");
            } else if (CommandLineOptions.Clo.TraceProofObligations) {
              int poCount = vcgen.CumulativeAssertionCount - prevAssertionCount;
              timeIndication = string.Format("  [{0} proof obligation{1}]  ", poCount, poCount == 1 ? "" : "s");
            }

            switch (outcome)
            {
                default:
                    Contract.Assert(false); throw new cce.UnreachableException();  // unexpected outcome
                case VCGen.Outcome.Correct:
                    printer.Inform(String.Format("{0}verified", timeIndication));
                    verified++;
                    break;
                case VCGen.Outcome.TimedOut:
                    timeOuts++;
                    printer.Inform(String.Format("{0}timed out", timeIndication));
                    break;
                case VCGen.Outcome.OutOfMemory:
                    outOfMemories++;
                    printer.Inform(String.Format("{0}out of memory", timeIndication));
                    break;
                case VCGen.Outcome.Inconclusive:
                    inconclusives++;
                    printer.Inform(String.Format("{0}inconclusive", timeIndication));
                    break;
                case VCGen.Outcome.Errors:
                    Contract.Assert(errors != null);  // guaranteed by postcondition of VerifyImplementation
                    break;
            }
            if (errors != null)
            {
              // BP1xxx: Parsing errors
              // BP2xxx: Name resolution errors
              // BP3xxx: Typechecking errors
              // BP4xxx: Abstract interpretation errors (Is there such a thing?)
              // BP5xxx: Verification errors

              var cause = "Error";
              if (outcome == VCGen.Outcome.TimedOut)
              {
                cause = "Timed out on";
              }
              else if (outcome == VCGen.Outcome.OutOfMemory)
              {
                cause = "Out of memory on";
              }

              errors.Sort(new CounterexampleComparer());
              foreach (Counterexample error in errors)
              {
                if (error is CallCounterexample)
                {
                  CallCounterexample err = (CallCounterexample)error;
                  ReportBplError(err.FailingCall.tok, (err.FailingCall.ErrorData as string) ?? cause + " BP5002: A precondition for this call might not hold.", true);
                  ReportBplError(err.FailingRequires.tok, (err.FailingRequires.ErrorData as string) ?? "Related location: This is the precondition that might not hold.", false);
                  if (CommandLineOptions.Clo.XmlSink != null)
                  {
                    CommandLineOptions.Clo.XmlSink.WriteError("precondition violation", err.FailingCall.tok, err.FailingRequires.tok, error.Trace);
                  }
                }
                else if (error is ReturnCounterexample)
                {
                  ReturnCounterexample err = (ReturnCounterexample)error;
                  ReportBplError(err.FailingReturn.tok, cause + " BP5003: A postcondition might not hold on this return path.", true);
                  ReportBplError(err.FailingEnsures.tok, (err.FailingEnsures.ErrorData as string) ?? "Related location: This is the postcondition that might not hold.", false);
                  ReportAllBplErrors(err.FailingEnsures.Attributes);
                  if (CommandLineOptions.Clo.XmlSink != null)
                  {
                    CommandLineOptions.Clo.XmlSink.WriteError("postcondition violation", err.FailingReturn.tok, err.FailingEnsures.tok, error.Trace);
                  }
                }
                else // error is AssertCounterexample
                {
                  AssertCounterexample err = (AssertCounterexample)error;
                  if (err.FailingAssert is LoopInitAssertCmd)
                  {
                    ReportBplError(err.FailingAssert.tok, cause + " BP5004: This loop invariant might not hold on entry.", true);
                    if (CommandLineOptions.Clo.XmlSink != null)
                    {
                      CommandLineOptions.Clo.XmlSink.WriteError("loop invariant entry violation", err.FailingAssert.tok, null, error.Trace);
                    }
                  }
                  else if (err.FailingAssert is LoopInvMaintainedAssertCmd)
                  {
                    // this assertion is a loop invariant which is not maintained
                    ReportBplError(err.FailingAssert.tok, cause + " BP5005: This loop invariant might not be maintained by the loop.", true);
                    if (CommandLineOptions.Clo.XmlSink != null)
                    {
                      CommandLineOptions.Clo.XmlSink.WriteError("loop invariant maintenance violation", err.FailingAssert.tok, null, error.Trace);
                    }
                  }
                  else
                  {
                    string msg = err.FailingAssert.ErrorData as string;
                    if (msg == null)
                    {
                      msg = cause + " BP5001: This assertion might not hold.";
                    }
                    ReportBplError(err.FailingAssert.tok, msg, true);
                    var attr = err.FailingAssert.Attributes;
                    ReportAllBplErrors(attr);
                    if (CommandLineOptions.Clo.XmlSink != null)
                    {
                      CommandLineOptions.Clo.XmlSink.WriteError("assertion violation", err.FailingAssert.tok, null, error.Trace);
                    }
                  }
                }
                if (CommandLineOptions.Clo.EnhancedErrorMessages == 1)
                {
                  foreach (string info in error.relatedInformation)
                  {
                    Contract.Assert(info != null);
                    Console.WriteLine("       " + info);
                  }
                }
                if (CommandLineOptions.Clo.ErrorTrace > 0)
                {
                  Console.WriteLine("Execution trace:");
                  foreach (Block b in error.Trace)
                  {
                    Contract.Assert(b != null);
                    if (b.tok == null)
                    {
                      Console.WriteLine("    <intermediate block>");
                    }
                    else
                    {
                      // for ErrorTrace == 1 restrict the output;
                      // do not print tokens with -17:-4 as their location because they have been
                      // introduced in the translation and do not give any useful feedback to the user
                      if (!(CommandLineOptions.Clo.ErrorTrace == 1 && b.tok.line == -17 && b.tok.col == -4))
                      {
                        Console.WriteLine("    {0}({1},{2}): {3}", b.tok.filename, b.tok.line, b.tok.col, b.Label);
                      }
                    }
                  }
                }
                if (CommandLineOptions.Clo.ModelViewFile != null)
                {
                  error.PrintModel();
                }
                if (cause == "Error")
                {
                  errorCount++;
                }
              }
              if (cause == "Error")
              {
                printer.Inform(String.Format("{0}error{1}", timeIndication, errors.Count == 1 ? "" : "s"));
              }
            }

            if (CommandLineOptions.Clo.XmlSink != null)
            {
                CommandLineOptions.Clo.XmlSink.WriteEndMethod(outcome.ToString().ToLowerInvariant(), end, elapsed);
            }
            if (outcome == VCGen.Outcome.Errors || CommandLineOptions.Clo.Trace)
            {
                Console.Out.Flush();
            }
        }
      }
      vcgen.Close();
      cce.NonNull(CommandLineOptions.Clo.TheProverFactory).Close();

      #endregion

      return PipelineOutcome.VerificationCompleted;
    }


    #region Output
    
    static OutputPrinter printer = new ConsolePrinter();

    #region Dafny output

    static void ReportAllBplErrors(QKeyValue attr)
    {
      while (attr != null)
      {
        if (attr.Key == "msg" && attr.Params.Count == 1)
        {
          var str = attr.Params[0] as string;
          if (str != null)
          {
            ReportBplError(attr.tok, "Error: " + str, false);
          }
        }
        attr = attr.Next;
      }
    }


    static void ReportBplError(IToken tok, string message, bool error)
    {
      Contract.Requires(message != null);
      string s;
      if (tok == null)
      {
        s = message;
      }
      else
      {
        s = string.Format("{0}({1},{2}): {3}", tok.filename, tok.line, tok.col, message);
      }
      if (error)
      {
        printer.ErrorWriteLine(s);
      }
      else
      {
        Console.WriteLine(s);
      }
      if (tok is Dafny.NestedToken)
      {
        var nt = (Dafny.NestedToken)tok;
        ReportBplError(nt.Inner, "Related location: Related location", false);
      }
    }

    #endregion

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
