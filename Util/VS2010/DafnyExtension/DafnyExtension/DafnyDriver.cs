using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;
using System.Diagnostics;
using System.Diagnostics.Contracts;
// Here come the Dafny/Boogie specific imports
//using PureCollections;
using Bpl = Microsoft.Boogie;
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

    static DafnyDriver() {
      Initialize();
    }

    static void Initialize() {
      if (Dafny.DafnyOptions.O == null) {
        Dafny.DafnyOptions.Install(new Dafny.DafnyOptions());
        Dafny.DafnyOptions.O.DafnyPrelude = "c:\\boogie\\Binaries\\DafnyPrelude.bpl";
        Dafny.DafnyOptions.O.ApplyDefaultOptions();
      }
    }

    public Dafny.Program Process() {
      if (!ParseAndTypeCheck()) {
        return null;
      }
      return _program;
    }

    bool ParseAndTypeCheck() {
      Dafny.ModuleDecl module = new Dafny.LiteralModuleDecl(new Dafny.DefaultModuleDecl(), null);
      Dafny.BuiltIns builtIns = new Dafny.BuiltIns();
      int errorCount = Dafny.Parser.Parse(_programText, _filename, module, builtIns, new VSErrors(this));
      if (errorCount != 0)
        return false;
      Dafny.Program program = new Dafny.Program(_filename, module, builtIns);

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
      public override void Error(Bpl.IToken tok, string msg, params object[] args) {
        string s = string.Format(msg, args);
        dd.RecordError(tok.line - 1, tok.col - 1, ErrorCategory.ResolveError, s);
        ErrorCount++;
      }
    }

    public static bool Verify(Dafny.Program dafnyProgram, ErrorReporterDelegate er) {
      Dafny.Translator translator = new Dafny.Translator();
      Bpl.Program boogieProgram = translator.Translate(dafnyProgram);

      int errorCount, verified, inconclusives, timeOuts, outOfMemories;
      PipelineOutcome oc = BoogiePipeline(boogieProgram, er, out errorCount, out verified, out inconclusives, out timeOuts, out outOfMemories);
      bool allOk = errorCount == 0 && inconclusives == 0 && timeOuts == 0 && outOfMemories == 0;
      // TODO:  This would be the place to proceed to compile the program, if desired
      return allOk;
    }

    enum PipelineOutcome { Done, ResolutionError, TypeCheckingError, ResolvedAndTypeChecked, FatalError, VerificationCompleted }

    /// <summary>
    /// Resolve, type check, infer invariants for, and verify the given Boogie program.
    /// The intention is that this Boogie program has been produced by translation from something
    /// else.  Hence, any resolution errors and type checking errors are due to errors in
    /// the translation.
    /// </summary>
    static PipelineOutcome BoogiePipeline(Bpl.Program/*!*/ program, ErrorReporterDelegate er,
        out int errorCount, out int verified, out int inconclusives, out int timeOuts, out int outOfMemories) {
      Contract.Requires(program != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out inconclusives) && 0 <= Contract.ValueAtReturn(out timeOuts));

      errorCount = verified = inconclusives = timeOuts = outOfMemories = 0;
      PipelineOutcome oc = BoogieResolveAndTypecheck(program);
      if (oc == PipelineOutcome.ResolvedAndTypeChecked) {
        EliminateDeadVariablesAndInline(program);
        return BoogieInferAndVerify(program, er, out errorCount, out verified, out inconclusives, out timeOuts, out outOfMemories);
      }
      return oc;
    }

    static void EliminateDeadVariablesAndInline(Bpl.Program program) {
      Contract.Requires(program != null);
      // Eliminate dead variables
      Microsoft.Boogie.UnusedVarEliminator.Eliminate(program);

      // Collect mod sets
      if (Bpl.CommandLineOptions.Clo.DoModSetAnalysis) {
        Microsoft.Boogie.ModSetCollector.DoModSetAnalysis(program);
      }

      // Coalesce blocks
      if (Bpl.CommandLineOptions.Clo.CoalesceBlocks) {
        Microsoft.Boogie.BlockCoalescer.CoalesceBlocks(program);
      }

      // Inline
      var TopLevelDeclarations = program.TopLevelDeclarations;

      if (Bpl.CommandLineOptions.Clo.ProcedureInlining != Bpl.CommandLineOptions.Inlining.None) {
        bool inline = false;
        foreach (var d in TopLevelDeclarations) {
          if (d.FindExprAttribute("inline") != null) {
            inline = true;
          }
        }
        if (inline && Bpl.CommandLineOptions.Clo.StratifiedInlining == 0) {
          foreach (var d in TopLevelDeclarations) {
            var impl = d as Bpl.Implementation;
            if (impl != null) {
              impl.OriginalBlocks = impl.Blocks;
              impl.OriginalLocVars = impl.LocVars;
            }
          }
          foreach (var d in TopLevelDeclarations) {
            var impl = d as Bpl.Implementation;
            if (impl != null && !impl.SkipVerification) {
              Bpl.Inliner.ProcessImplementation(program, impl);
            }
          }
          foreach (var d in TopLevelDeclarations) {
            var impl = d as Bpl.Implementation;
            if (impl != null) {
              impl.OriginalBlocks = null;
              impl.OriginalLocVars = null;
            }
          }
        }
      }
    }

    /// <summary>
    /// Resolves and type checks the given Boogie program.
    /// Returns:
    ///  - Done if no errors occurred, and command line specified no resolution or no type checking.
    ///  - ResolutionError if a resolution error occurred
    ///  - TypeCheckingError if a type checking error occurred
    ///  - ResolvedAndTypeChecked if both resolution and type checking succeeded
    /// </summary>
    static PipelineOutcome BoogieResolveAndTypecheck(Bpl.Program program) {
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
    ///  - FatalError if a fatal error occurred
    ///  - VerificationCompleted if inference and verification completed, in which the out
    ///    parameters contain meaningful values
    /// </summary>
    static PipelineOutcome BoogieInferAndVerify(Bpl.Program program, ErrorReporterDelegate er,
                                                out int errorCount, out int verified, out int inconclusives, out int timeOuts, out int outOfMemories) {
      Contract.Requires(program != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out inconclusives) && 0 <= Contract.ValueAtReturn(out timeOuts));

      errorCount = verified = inconclusives = timeOuts = outOfMemories = 0;

      // ---------- Infer invariants --------------------------------------------------------

      // Abstract interpretation -> Always use (at least) intervals, if not specified otherwise (e.g. with the "/noinfer" switch)
      if (Bpl.CommandLineOptions.Clo.UseAbstractInterpretation) {
        if (Bpl.CommandLineOptions.Clo.Ai.J_Intervals || Bpl.CommandLineOptions.Clo.Ai.J_Trivial) {
          Microsoft.Boogie.AbstractInterpretation.NativeAbstractInterpretation.RunAbstractInterpretation(program);
        } else if (Bpl.CommandLineOptions.Clo.Ai.AnySet) {
          // run one of the old domains
          Microsoft.Boogie.AbstractInterpretation.AbstractInterpretation.RunAbstractInterpretation(program);
        } else {
          // use /infer:j as the default
          Bpl.CommandLineOptions.Clo.Ai.J_Intervals = true;
          Microsoft.Boogie.AbstractInterpretation.NativeAbstractInterpretation.RunAbstractInterpretation(program);
        }
      }

      if (Bpl.CommandLineOptions.Clo.LoopUnrollCount != -1) {
        program.UnrollLoops(Bpl.CommandLineOptions.Clo.LoopUnrollCount);
      }

      if (Bpl.CommandLineOptions.Clo.ExpandLambdas) {
        Bpl.LambdaHelper.ExpandLambdas(program);
        //PrintBplFile ("-", program, true);
      }

      // ---------- Verify ------------------------------------------------------------

      if (!Bpl.CommandLineOptions.Clo.Verify) { return PipelineOutcome.Done; }

      #region Verify each implementation

      ConditionGeneration vcgen = null;
      try {
        if (Bpl.CommandLineOptions.Clo.vcVariety == Bpl.CommandLineOptions.VCVariety.Doomed) {
          vcgen = new DCGen(program, Bpl.CommandLineOptions.Clo.SimplifyLogFilePath, Bpl.CommandLineOptions.Clo.SimplifyLogFileAppend);
        } else {
          vcgen = new VCGen(program, Bpl.CommandLineOptions.Clo.SimplifyLogFilePath, Bpl.CommandLineOptions.Clo.SimplifyLogFileAppend);
        }
      } catch (Bpl.ProverException) {
        return PipelineOutcome.FatalError;
      }

      var decls = program.TopLevelDeclarations.ToArray();
      foreach (var decl in decls) {
        Contract.Assert(decl != null);
        Bpl.Implementation impl = decl as Bpl.Implementation;
        if (impl != null && Bpl.CommandLineOptions.Clo.UserWantsToCheckRoutine(impl.Name) && !impl.SkipVerification) {
          List<Bpl.Counterexample>/*?*/ errors;

          ConditionGeneration.Outcome outcome;
          int prevAssertionCount = vcgen.CumulativeAssertionCount;
          try {
            outcome = vcgen.VerifyImplementation(impl, out errors);
          } catch (VCGenException) {
            errors = null;
            outcome = VCGen.Outcome.Inconclusive;
          } catch (Bpl.UnexpectedProverOutputException) {
            errors = null;
            outcome = VCGen.Outcome.Inconclusive;
          }

          switch (outcome) {
            default:
              Contract.Assert(false); throw new Exception();  // unexpected outcome
            case VCGen.Outcome.Correct:
              verified++;
              break;
            case VCGen.Outcome.TimedOut:
              timeOuts++;
              break;
            case VCGen.Outcome.OutOfMemory:
              outOfMemories++;
              break;
            case VCGen.Outcome.Inconclusive:
              inconclusives++;
              break;
            case VCGen.Outcome.Errors:
              Contract.Assert(errors != null);  // guaranteed by postcondition of VerifyImplementation

              errors.Sort(new Bpl.CounterexampleComparer());
              foreach (var error in errors) {
                DafnyErrorInformation errorInfo;

                if (error is Bpl.CallCounterexample) {
                  var err = (Bpl.CallCounterexample)error;
                  errorInfo = new DafnyErrorInformation(err.FailingCall.tok, err.FailingCall.ErrorData as string ?? "A precondition for this call might not hold.");
                  errorInfo.AddAuxInfo(err.FailingRequires.tok, err.FailingRequires.ErrorData as string ?? "Related location: This is the precondition that might not hold.");

                } else if (error is Bpl.ReturnCounterexample) {
                  var err = (Bpl.ReturnCounterexample)error;
                  errorInfo = new DafnyErrorInformation(err.FailingReturn.tok, "A postcondition might not hold on this return path.");
                  errorInfo.AddAuxInfo(err.FailingEnsures.tok, err.FailingEnsures.ErrorData as string ?? "Related location: This is the postcondition that might not hold.");
                  errorInfo.AddAuxInfo(err.FailingEnsures.Attributes);

                } else { // error is AssertCounterexample
                  var err = (Bpl.AssertCounterexample)error;
                  if (err.FailingAssert is Bpl.LoopInitAssertCmd) {
                    errorInfo = new DafnyErrorInformation(err.FailingAssert.tok, "This loop invariant might not hold on entry.");
                  } else if (err.FailingAssert is Bpl.LoopInvMaintainedAssertCmd) {
                    // this assertion is a loop invariant which is not maintained
                    errorInfo = new DafnyErrorInformation(err.FailingAssert.tok, "This loop invariant might not be maintained by the loop.");
                  } else {
                    string msg = err.FailingAssert.ErrorData as string;
                    if (msg == null) {
                      msg = "This assertion might not hold.";
                    }
                    errorInfo = new DafnyErrorInformation(err.FailingAssert.tok, msg);
                    errorInfo.AddAuxInfo(err.FailingAssert.Attributes);
                  }
                }
                if (Bpl.CommandLineOptions.Clo.ErrorTrace > 0) {
                  foreach (Bpl.Block b in error.Trace) {
                    // for ErrorTrace == 1 restrict the output;
                    // do not print tokens with -17:-4 as their location because they have been
                    // introduced in the translation and do not give any useful feedback to the user
                    if (!(Bpl.CommandLineOptions.Clo.ErrorTrace == 1 && b.tok.line == -17 && b.tok.col == -4) &&
                        b.tok.line != 0 && b.tok.col != 0) {
                      errorInfo.AddAuxInfo(b.tok, "Execution trace: " + b.Label);
                    }
                  }
                }
                // if (Bpl.CommandLineOptions.Clo.ModelViewFile != null) {
                //   error.PrintModel();
                // }
                er(errorInfo);
                errorCount++;
              }
              break;
          }
        }
      }
      vcgen.Close();
      Bpl.CommandLineOptions.Clo.TheProverFactory.Close();

      #endregion

      return PipelineOutcome.VerificationCompleted;
    }

    public delegate void ErrorReporterDelegate(DafnyErrorInformation errInfo);

    public class DafnyErrorInformation
    {
      public readonly Bpl.IToken Tok;
      public readonly string Msg;
      public readonly List<DafnyErrorAuxInfo> Aux = new List<DafnyErrorAuxInfo>();

      public class DafnyErrorAuxInfo
      {
        public readonly Bpl.IToken Tok;
        public readonly string Msg;
        public DafnyErrorAuxInfo(Bpl.IToken tok, string msg) {
          Tok = tok;
          Msg = CleanUp(msg);
        }
      }

      public DafnyErrorInformation(Bpl.IToken tok, string msg) {
        Contract.Requires(tok != null);
        Contract.Requires(1 <= tok.line && 1 <= tok.col);
        Contract.Requires(msg != null);
        Tok = tok;
        Msg = CleanUp(msg);
      }
      public void AddAuxInfo(Bpl.IToken tok, string msg) {
        Contract.Requires(tok != null);
        Contract.Requires(1 <= tok.line && 1 <= tok.col);
        Contract.Requires(msg != null);
        Aux.Add(new DafnyErrorAuxInfo(tok, msg));
      }
      public void AddAuxInfo(Bpl.QKeyValue attr) {
        while (attr != null) {
          if (attr.Key == "msg" && attr.Params.Count == 1 && attr.tok.line != 0 && attr.tok.col != 0) {
            var str = attr.Params[0] as string;
            if (str != null) {
              AddAuxInfo(attr.tok, str);
            }
          }
          attr = attr.Next;
        }
      }

      public static string CleanUp(string msg) {
        if (msg.ToLower().StartsWith("error: ")) {
          return msg.Substring(7);
        } else {
          return msg;
        }
      }
    }
  }
}
