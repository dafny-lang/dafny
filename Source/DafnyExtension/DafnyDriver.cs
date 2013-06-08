using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.VisualStudio.Text;
using VC;
using Bpl = Microsoft.Boogie;
using Dafny = Microsoft.Dafny;


namespace DafnyLanguage
{
  public class DafnyDriver
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
        var options = new Dafny.DafnyOptions();
        options.ProverKillTime = 10;
        options.ErrorTrace = 0;
        Dafny.DafnyOptions.Install(options);
        options.ApplyDefaultOptions();

        ExecutionEngine.printer = new ConsolePrinter();
        // TODO(wuestholz): Turn this on as soon as the error locations are updated properly.
        // Dafny.DafnyOptions.Clo.VerifySnapshots = true;
      }
    }

    internal Dafny.Program ProcessResolution() {
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

    class DafnyErrorInformationFactory : ErrorInformationFactory
    {
      public override ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId)
      {
        return new DafnyErrorInformation(tok, msg, requestId);
      }
    }
    
    class DafnyErrorInformation : ErrorInformation
    {
      public DafnyErrorInformation(IToken tok, string msg, string requestId)
        : base(tok, msg)
      {
        RequestId = requestId;
        AddNestingsAsAux(tok);
      }

      public override void AddAuxInfo(IToken tok, string msg)
      {
        base.AddAuxInfo(tok, msg);
        AddNestingsAsAux(tok);
      }

      void AddNestingsAsAux(IToken tok)
      {
        while (tok != null && tok is Dafny.NestedToken)
        {
          var nt = (Dafny.NestedToken)tok;
          tok = nt.Inner;
          Aux.Add(new AuxErrorInfo(tok, "Related location"));
        }
      }
    }

    #region Compilation

    public static void Compile(Dafny.Program dafnyProgram)
    {
      Microsoft.Dafny.DafnyOptions.O.SpillTargetCode = true;
      Microsoft.Dafny.DafnyDriver.CompileDafnyProgram(dafnyProgram, dafnyProgram.Name);
    }

    #endregion

    #region Boogie interaction

    public static ConcurrentDictionary<string, ITextSnapshot> RequestIdToSnapshot = new ConcurrentDictionary<string, ITextSnapshot>();

    public static bool Verify(Dafny.Program dafnyProgram, ITextSnapshot snapshot, ErrorReporterDelegate er) {
      Dafny.Translator translator = new Dafny.Translator();
      translator.InsertChecksums = true;
      Bpl.Program boogieProgram = translator.Translate(dafnyProgram);

      PipelineOutcome oc = BoogiePipeline(boogieProgram, snapshot, er);
      switch (oc) {
        case PipelineOutcome.Done:
        case PipelineOutcome.VerificationCompleted:
          // TODO:  This would be the place to proceed to compile the program, if desired
          return true;
        case PipelineOutcome.FatalError:
        default:
          return false;
      }
    }

    /// <summary>
    /// Resolve, type check, infer invariants for, and verify the given Boogie program.
    /// The intention is that this Boogie program has been produced by translation from something
    /// else.  Hence, any resolution errors and type checking errors are due to errors in
    /// the translation.
    /// </summary>
    static PipelineOutcome BoogiePipeline(Bpl.Program/*!*/ program, ITextSnapshot snapshot, ErrorReporterDelegate er) {
      Contract.Requires(program != null);

      PipelineOutcome oc = BoogieResolveAndTypecheck(program);
      if (oc == PipelineOutcome.ResolvedAndTypeChecked) {
        ExecutionEngine.EliminateDeadVariablesAndInline(program);
        ExecutionEngine.errorInformationFactory = new DafnyErrorInformationFactory();
        int errorCount, verified, inconclusives, timeOuts, outOfMemories;
        var requestId = (RequestIdToSnapshot.Count + 1).ToString();
        RequestIdToSnapshot[requestId] = snapshot;
        return ExecutionEngine.InferAndVerify(program, out errorCount, out verified, out inconclusives, out timeOuts, out outOfMemories, er, requestId);
      }
      return oc;
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

    #endregion
  }
}
