using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;
using System.Diagnostics.Contracts;
// Here come the Dafny/Boogie specific imports
//using PureCollections;
using Microsoft.Boogie;
using Dafny = Microsoft.Dafny;
using Microsoft.Boogie.AbstractInterpretation;
using VC;
// using AI = Microsoft.AbstractInterpretationFramework;


namespace DafnyLanguage
{
  class DafnyDriver
  {
    readonly string _programText;
    readonly string _filename;
    Dafny.Program _program;
    List<DafnyError> _errors = new List<DafnyError>();
    public List<DafnyError> Errors { get { return _errors; } }

    public DafnyDriver(string programText, string filename) {
      _programText = programText;
      _filename = filename;
    }

    void RecordError(int line, int col, ErrorCategory cat, string msg) {
      _errors.Add(new DafnyError(line, col, cat, msg));
    }

    void RecordProcessError(string msg) {
      RecordError(0, 0, ErrorCategory.ProcessError, msg);
    }

    public void Process_ViaBatchFile() {
      if (!File.Exists(@"C:\tmp\StartDafny.bat")) {
        RecordProcessError(@"Can't find C:\tmp\StartDafny.bat");
      }

      // From: http://dotnetperls.com/process-redirect-standard-output
      // (Also, see: http://msdn.microsoft.com/en-us/library/system.diagnostics.processstartinfo.redirectstandardoutput.aspx)
      //
      // Setup the process with the ProcessStartInfo class.
      //
      ProcessStartInfo start = new ProcessStartInfo();
      start.FileName = @"cmd.exe";
      start.Arguments = @"/c C:\tmp\StartDafny.bat"; // Specify exe name.
      start.UseShellExecute = false;
      start.RedirectStandardInput = true;
      start.RedirectStandardOutput = true;
      start.CreateNoWindow = true;
      //
      // Start the process.
      //
      using (System.Diagnostics.Process process = System.Diagnostics.Process.Start(start)) {
        //
        // Push the file contents to the new process
        //
        StreamWriter myStreamWriter = process.StandardInput;
        myStreamWriter.WriteLine(_programText);
        myStreamWriter.Close();
        //
        // Read in all the text from the process with the StreamReader.
        //
        using (StreamReader reader = process.StandardOutput) {
          for (string line = reader.ReadLine(); !String.IsNullOrEmpty(line); line = reader.ReadLine()) {
            // the lines of interest have the form "filename(line,col): some_error_label: error_message"
            // where "some_error_label" is "Error" or "syntax error" or "Error BP5003" or "Related location"
            string message;
            int n = line.IndexOf("): ", 2);  // we start at 2, to avoid problems with "C:\..."
            if (n == -1) {
              continue;
            } else {
              int m = line.IndexOf(": ", n + 3);
              if (m == -1) {
                continue;
              }
              message = line.Substring(m + 2);
            }
            line = line.Substring(0, n);  // line now has the form "filename(line,col"

            n = line.LastIndexOf(',');
            if (n == -1) { continue; }
            var colString = line.Substring(n + 1);
            line = line.Substring(0, n);  // line now has the form "filename(line"

            n = line.LastIndexOf('(');
            if (n == -1) { continue; }
            var lineString = line.Substring(n + 1);

            try {
              int errLine = Int32.Parse(lineString) - 1;
              int errCol = Int32.Parse(colString) - 1;
              RecordError(errLine, errCol, message.StartsWith("syntax error") ? ErrorCategory.ParseError : ErrorCategory.VerificationError, message);
            } catch (System.FormatException) {
              continue;
            } catch (System.OverflowException) {
              continue;
            }
          }
        }
      }
    }

    static DafnyDriver() {
      Initialize();
    }

    static void Initialize() {
      CommandLineOptions.Clo.RunningBoogieOnSsc = false;
      CommandLineOptions.Clo.TheProverFactory = ProverFactory.Load("Z3");
      CommandLineOptions.Clo.ProverName = "Z3";
      CommandLineOptions.Clo.vcVariety = CommandLineOptions.Clo.TheProverFactory.DefaultVCVariety;
    }

    public Dafny.Program Process() {
      if (!ParseAndTypeCheck()) {
        return null;
      }
      return _program;
    }

    bool ParseAndTypeCheck() {
      List<Dafny.ModuleDecl> modules = new List<Dafny.ModuleDecl>();
      Dafny.BuiltIns builtIns = new Dafny.BuiltIns();
      int errorCount = Dafny.Parser.Parse(_programText, _filename, modules, builtIns, new VSErrors(this));
      if (errorCount != 0)
        return false;
      Dafny.Program program = new Dafny.Program(_filename, modules, builtIns);

      Dafny.Resolver r = new VSResolver(program, this);
      r.ResolveProgram(program);
      if (r.ErrorCount != 0)
        return false;

      _program = program;
      return true;  // success
    }

    class VSErrors : Dafny.Errors
    {
      DafnyDriver dd;
      public VSErrors(DafnyDriver dd) {
        this.dd = dd;
      }
      public override void SynErr(string filename, int line, int col, string msg) {
        dd.RecordError(line - 1, col - 1, ErrorCategory.ParseError, msg);
        count++;
      }
      public override void SemErr(string filename, int line, int col, string msg) {
        dd.RecordError(line - 1, col - 1, ErrorCategory.ResolveError, msg);
        count++;
      }
      public override void Warning(string filename, int line, int col, string msg) {
        dd.RecordError(line - 1, col - 1, ErrorCategory.ParseWarning, msg);
      }
    }

    class VSResolver : Dafny.Resolver
    {
      DafnyDriver dd;
      public VSResolver(Dafny.Program program, DafnyDriver dd)
        : base(program) {
        this.dd = dd;
      }
      protected override void Error(IToken tok, string msg, params object[] args) {
        string s = string.Format(msg, args);
        dd.RecordError(tok.line - 1, tok.col - 1, ErrorCategory.ResolveError, s);
        ErrorCount++;
      }
    }

#if LATER
    static bool Verify(Microsoft.Dafny.Program dafnyProgram) {
      Dafny.Translator translator = new Dafny.Translator();
      Program boogieProgram = translator.Translate(dafnyProgram);

      int errorCount, verified, inconclusives, timeOuts, outOfMemories;
      PipelineOutcome oc = BoogiePipeline(boogieProgram, out errorCount, out verified, out inconclusives, out timeOuts, out outOfMemories);
      switch (oc) {
        case PipelineOutcome.VerificationCompleted:
        case PipelineOutcome.Done:  // (this says not to continue with compilation)
          // WriteTrailer(verified, errorCount, inconclusives, timeOuts, outOfMemories);
          break;
        default:
          // error has already been reported to user
          break;
      }
      return errorCount == 0 && inconclusives == 0 && timeOuts == 0 && outOfMemories == 0;
    }

    /// <summary>
    /// Resolve, type check, infer invariants for, and verify the given Boogie program.
    /// The intention is that this Boogie program has been produced by translation from something
    /// else.  Hence, any resolution errors and type checking errors are due to errors in
    /// the translation.
    /// </summary>
    static PipelineOutcome BoogiePipeline(Program/*!*/ program,
        out int errorCount, out int verified, out int inconclusives, out int timeOuts, out int outOfMemories) {
      Contract.Requires(program != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out inconclusives) && 0 <= Contract.ValueAtReturn(out timeOuts));

      errorCount = verified = inconclusives = timeOuts = outOfMemories = 0;
      PipelineOutcome oc = ResolveAndTypecheck(program);
      switch (oc) {
        case PipelineOutcome.Done:
          return oc;

        case PipelineOutcome.ResolutionError:
        case PipelineOutcome.TypeCheckingError:
          // the Dafny-to-Boogie translation must have been bad; this is an internal error
          return oc;

        case PipelineOutcome.ResolvedAndTypeChecked:
          return InferAndVerify(program, out errorCount, out verified, out inconclusives, out timeOuts, out outOfMemories);

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected outcome
      }
    }


    enum PipelineOutcome { Done, ResolutionError, TypeCheckingError, ResolvedAndTypeChecked, FatalError, VerificationCompleted }

    /// <summary>
    /// Resolves and type checks the given Boogie program.  Any errors are reported to the
    /// console.  Returns:
    ///  - Done if no errors occurred, and command line specified no resolution or no type checking.
    ///  - ResolutionError if a resolution error occurred
    ///  - TypeCheckingError if a type checking error occurred
    ///  - ResolvedAndTypeChecked if both resolution and type checking succeeded
    /// </summary>
    static PipelineOutcome ResolveAndTypecheck(Program program) {
      Contract.Requires(program != null);
      // ---------- Resolve ------------------------------------------------------------

      int errorCount = program.Resolve();
      if (errorCount != 0) {
        return PipelineOutcome.ResolutionError;
      }

      // ---------- Type check ------------------------------------------------------------

      errorCount = program.Typecheck();
      if (errorCount != 0) {
        return PipelineOutcome.TypeCheckingError;
      }

      return PipelineOutcome.ResolvedAndTypeChecked;
    }

    /// <summary>
    /// Given a resolved and type checked Boogie program, infers invariants for the program
    /// and then attempts to verify it.  Returns:
    ///  - Done if command line specified no verification
    ///  - FatalError if a fatal error occurred, in which case an error has been printed to console
    ///  - VerificationCompleted if inference and verification completed, in which the out
    ///    parameters contain meaningful values
    /// </summary>
    static PipelineOutcome InferAndVerify(Program program,
                                           out int errorCount, out int verified, out int inconclusives, out int timeOuts, out int outOfMemories) {
      Contract.Requires(program != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out inconclusives) && 0 <= Contract.ValueAtReturn(out timeOuts));

      errorCount = verified = inconclusives = timeOuts = outOfMemories = 0;

      // ---------- Infer invariants --------------------------------------------------------

      // Abstract interpretation -> Always use (at least) intervals, if not specified otherwise (e.g. with the "/noinfer" switch)
      Microsoft.Boogie.AbstractInterpretation.AbstractInterpretation.RunAbstractInterpretation(program);

      if (CommandLineOptions.Clo.ExpandLambdas) {
        LambdaHelper.ExpandLambdas(program);
      }

      // ---------- Verify ------------------------------------------------------------

    #region Verify each implementation

      ConditionGeneration vcgen = null;
      try {
        if (CommandLineOptions.Clo.vcVariety == CommandLineOptions.VCVariety.Doomed) {
          vcgen = new DCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend);
        } else {
          vcgen = new VCGen(program, CommandLineOptions.Clo.SimplifyLogFilePath, CommandLineOptions.Clo.SimplifyLogFileAppend);
        }
      } catch (ProverException e) {
        ErrorWriteLine("Fatal Error: ProverException: {0}", e);
        return PipelineOutcome.FatalError;
      }

      foreach (Declaration decl in program.TopLevelDeclarations) {
        Contract.Assert(decl != null);
        Implementation impl = decl as Implementation;
        if (impl != null && CommandLineOptions.Clo.UserWantsToCheckRoutine(cce.NonNull(impl.Name)) && !impl.SkipVerification) {
          List<Counterexample>/*?*/ errors;

          DateTime start = new DateTime();  // to please compiler's definite assignment rules
          if (CommandLineOptions.Clo.Trace || CommandLineOptions.Clo.XmlSink != null) {
            start = DateTime.Now;
            if (CommandLineOptions.Clo.Trace) {
              Console.WriteLine();
              Console.WriteLine("Verifying {0} ...", impl.Name);
            }
            if (CommandLineOptions.Clo.XmlSink != null) {
              CommandLineOptions.Clo.XmlSink.WriteStartMethod(impl.Name, start);
            }
          }

          ConditionGeneration.Outcome outcome;
          try {
            outcome = vcgen.VerifyImplementation(impl, program, out errors);
          } catch (VCGenException e) {
            ReportBplError(impl, String.Format("Error BP5010: {0}  Encountered in implementation {1}.", e.Message, impl.Name), true);
            errors = null;
            outcome = VCGen.Outcome.Inconclusive;
          } catch (UnexpectedProverOutputException upo) {
            AdvisoryWriteLine("Advisory: {0} SKIPPED because of internal error: unexpected prover output: {1}", impl.Name, upo.Message);
            errors = null;
            outcome = VCGen.Outcome.Inconclusive;
          }

          string timeIndication = "";
          DateTime end = DateTime.Now;
          TimeSpan elapsed = end - start;
          if (CommandLineOptions.Clo.Trace || CommandLineOptions.Clo.XmlSink != null) {
            if (CommandLineOptions.Clo.Trace) {
              timeIndication = string.Format("  [{0} s]  ", elapsed.TotalSeconds);
            }
          }


          switch (outcome) {
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected outcome
            case VCGen.Outcome.Correct:
              Inform(String.Format("{0}verified", timeIndication));
              verified++;
              break;
            case VCGen.Outcome.TimedOut:
              timeOuts++;
              Inform(String.Format("{0}timed out", timeIndication));
              break;
            case VCGen.Outcome.OutOfMemory:
              outOfMemories++;
              Inform(String.Format("{0}out of memory", timeIndication));
              break;
            case VCGen.Outcome.Inconclusive:
              inconclusives++;
              Inform(String.Format("{0}inconclusive", timeIndication));
              break;
            case VCGen.Outcome.Errors:
              Contract.Assert(errors != null);  // guaranteed by postcondition of VerifyImplementation
                // BP1xxx: Parsing errors
                // BP2xxx: Name resolution errors
                // BP3xxx: Typechecking errors
                // BP4xxx: Abstract interpretation errors (Is there such a thing?)
                // BP5xxx: Verification errors

                errors.Sort(new CounterexampleComparer());
                foreach (Counterexample error in errors) {
                  if (error is CallCounterexample) {
                    CallCounterexample err = (CallCounterexample)error;
                    ReportBplError(err.FailingCall, "Error BP5002: A precondition for this call might not hold.", true);
                    ReportBplError(err.FailingRequires, "Related location: This is the precondition that might not hold.", false);
                  } else if (error is ReturnCounterexample) {
                    ReturnCounterexample err = (ReturnCounterexample)error;
                    ReportBplError(err.FailingReturn, "Error BP5003: A postcondition might not hold on this return path.", true);
                    ReportBplError(err.FailingEnsures, "Related location: This is the postcondition that might not hold.", false);
                  } else // error is AssertCounterexample
                  {
                    AssertCounterexample err = (AssertCounterexample)error;
                    if (err.FailingAssert is LoopInitAssertCmd) {
                      ReportBplError(err.FailingAssert, "Error BP5004: This loop invariant might not hold on entry.", true);
                    } else if (err.FailingAssert is LoopInvMaintainedAssertCmd) {
                      // this assertion is a loop invariant which is not maintained
                      ReportBplError(err.FailingAssert, "Error BP5005: This loop invariant might not be maintained by the loop.", true);
                    } else {
                      string msg = err.FailingAssert.ErrorData as string;
                      if (msg == null) {
                        msg = "Error BP5001: This assertion might not hold.";
                      }
                      ReportBplError(err.FailingAssert, msg, true);
                    }
                  }
                  if (CommandLineOptions.Clo.ErrorTrace > 0) {
                    Console.WriteLine("Execution trace:");
                    foreach (Block b in error.Trace) {
                      Contract.Assert(b != null);
                      if (b.tok == null) {
                        Console.WriteLine("    <intermediate block>");
                      } else {
                        // for ErrorTrace == 1 restrict the output;
                        // do not print tokens with -17:-4 as their location because they have been 
                        // introduced in the translation and do not give any useful feedback to the user
                        if (!(CommandLineOptions.Clo.ErrorTrace == 1 && b.tok.line == -17 && b.tok.col == -4)) {
                          Console.WriteLine("    {0}({1},{2}): {3}", b.tok.filename, b.tok.line, b.tok.col, b.Label);
                        }
                      }
                    }
                  }
                  errorCount++;
                }
              Inform(String.Format("{0}error{1}", timeIndication, errors.Count == 1 ? "" : "s"));
              break;
          }
          if (outcome == VCGen.Outcome.Errors || CommandLineOptions.Clo.Trace) {
            Console.Out.Flush();
          }
        }
      }
      vcgen.Close();
      cce.NonNull(CommandLineOptions.Clo.TheProverFactory).Close();

    #endregion

      return PipelineOutcome.VerificationCompleted;
    }

    static void ReportBplError(Absy node, string message, bool error) {
      Contract.Requires(node != null); Contract.Requires(message != null);
      IToken tok = node.tok;
      string s;
      if (tok == null) {
        s = message;
      } else {
        s = string.Format("{0}({1},{2}): {3}", tok.filename, tok.line, tok.col, message);
      }
      if (error) {
        ErrorWriteLine(s);
      } else {
        Console.WriteLine(s);
      }
    }

    /// <summary>
    /// Inform the user about something and proceed with translation normally.
    /// Print newline after the message.
    /// </summary>
    public static void Inform(string s) {
      if (CommandLineOptions.Clo.Trace) {
        Console.WriteLine(s);
      }
    }
#endif
  }
}
