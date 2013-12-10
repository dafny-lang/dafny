using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.VisualStudio.Text;
using Bpl = Microsoft.Boogie;
using Dafny = Microsoft.Dafny;


namespace DafnyLanguage
{

  public class DafnyDriver
  {
    readonly string _filename;
    readonly ITextSnapshot _snapshot;
    Dafny.Program _program;

    List<DafnyError> _errors = new List<DafnyError>();
    public List<DafnyError> Errors { get { return _errors; } }

    public DafnyDriver(ITextSnapshot snapshot, string filename) {
      _snapshot = snapshot;
      _filename = filename;
    }

    static DafnyDriver() {
      // TODO(wuestholz): Do we really need to initialze this here?
      Initialize();
    }

    static void Initialize() {
      if (Dafny.DafnyOptions.O == null) {
        var options = new Dafny.DafnyOptions();
        options.ProverKillTime = 10;
        options.ErrorTrace = 0;
        options.VcsCores = System.Environment.ProcessorCount;
        options.ModelViewFile = "-";
        Dafny.DafnyOptions.Install(options);
        options.ApplyDefaultOptions();

        ExecutionEngine.printer = new DummyPrinter();
        ExecutionEngine.errorInformationFactory = new DafnyErrorInformationFactory();
        ToggleIncrementalVerification();
      }
    }


    #region Output

    class DummyPrinter : OutputPrinter
    {
      public void AdvisoryWriteLine(string format, params object[] args)
      {
      }

      public void ErrorWriteLine(TextWriter tw, string format, params object[] args)
      {
      }

      public void ErrorWriteLine(TextWriter tw, string s)
      {
      }

      public void Inform(string s, TextWriter tw)
      {
      }

      public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null)
      {
      }

      public void WriteTrailer(PipelineStatistics stats)
      {
      }

      public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true)
      {
      }
    }

    #endregion

    #region Parsing and type checking

    internal Dafny.Program ProcessResolution() {
      if (!ParseAndTypeCheck()) {
        return null;
      }
      return _program;
    }

    bool ParseAndTypeCheck() {
      Dafny.ModuleDecl module = new Dafny.LiteralModuleDecl(new Dafny.DefaultModuleDecl(), null);
      Dafny.BuiltIns builtIns = new Dafny.BuiltIns();
      Dafny.Errors parseErrors = new VSErrors(this);
      int errorCount = Dafny.Parser.Parse(_snapshot.GetText(), _filename, module, builtIns, parseErrors);
      string errString = Dafny.Main.ParseIncludes(module, builtIns, parseErrors);
      if (errorCount != 0 || errString != null)
        return false;
      Dafny.Program program = new Dafny.Program(_filename, module, builtIns);

      var r = new VSResolver(program, this);
      r.ResolveProgram(program);
      if (r.ErrorCount != 0)
        return false;

      program.AdditionalInformation.AddRange(r.AdditionalInformation);
      _program = program;
      return true;  // success
    }

    void RecordError(string filename, int line, int col, ErrorCategory cat, string msg)
    {
      _errors.Add(new DafnyError(filename, line, col, cat, msg, _snapshot, null, System.IO.Path.GetFullPath(this._filename) == filename));
    }

    class VSErrors : Dafny.Errors
    {
      DafnyDriver dd;
      public VSErrors(DafnyDriver dd) {
        this.dd = dd;
      }
      public override void SynErr(string filename, int line, int col, string msg) {
        dd.RecordError(filename, line - 1, col - 1, ErrorCategory.ParseError, msg);
        count++;
      }
      public override void SemErr(string filename, int line, int col, string msg) {
        dd.RecordError(filename, line - 1, col - 1, ErrorCategory.ResolveError, msg);
        count++;
      }
      public override void Warning(string filename, int line, int col, string msg) {
        dd.RecordError(filename, line - 1, col - 1, ErrorCategory.ParseWarning, msg);
      }
    }

    class VSResolver : Dafny.Resolver
    {
      DafnyDriver dd;
      Dictionary<IToken, HashSet<AdditionalInformation>> _additionalInformation = new Dictionary<IToken, HashSet<AdditionalInformation>>();
      public List<AdditionalInformation> AdditionalInformation { get { return _additionalInformation.Values.SelectMany(i => i).ToList(); } }

      public VSResolver(Dafny.Program program, DafnyDriver dd)
        : base(program) {
        this.dd = dd;

        AdditionalInformationReporter =
          (addinfo)
            =>
            {
              if (!_additionalInformation.ContainsKey(addinfo.Token)) {
                _additionalInformation.Add(addinfo.Token, new HashSet<AdditionalInformation>());
              }
              _additionalInformation[addinfo.Token].Add(addinfo);
            };
      }

      public override void Error(Bpl.IToken tok, string msg, params object[] args) {
        string s = string.Format(msg, args);
        dd.RecordError(tok.filename, tok.line - 1, tok.col - 1, ErrorCategory.ResolveError, s);
        ErrorCount++;
      }
    }

    #endregion

    #region Compilation

    public static void Compile(Dafny.Program dafnyProgram)
    {
      Microsoft.Dafny.DafnyOptions.O.SpillTargetCode = true;
      Microsoft.Dafny.DafnyDriver.CompileDafnyProgram(dafnyProgram, dafnyProgram.Name);
    }

    #endregion

    #region Boogie interaction

    class DafnyErrorInformationFactory : ErrorInformationFactory
    {
      public override ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId, string category = null)
      {
        return new DafnyErrorInformation(tok, msg, requestId, category);
      }
    }

    class DafnyErrorInformation : ErrorInformation
    {
      public DafnyErrorInformation(IToken tok, string msg, string requestId, string category = null)
        : base(tok, msg)
      {
        RequestId = requestId;
        Category = category;
        AddNestingsAsAux(tok);
      }

      public override void AddAuxInfo(IToken tok, string msg, string category = null)
      {
        base.AddAuxInfo(tok, msg, category);
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

    public static bool ToggleIncrementalVerification()
    {
      Dafny.DafnyOptions.Clo.VerifySnapshots = !Dafny.DafnyOptions.Clo.VerifySnapshots;
      return Dafny.DafnyOptions.Clo.VerifySnapshots;
    }

    public static bool Verify(Dafny.Program dafnyProgram, ResolverTagger resolver, string uniqueIdPrefix, string requestId, ErrorReporterDelegate er) {
      Dafny.Translator translator = new Dafny.Translator();
      translator.InsertChecksums = true;
      translator.UniqueIdPrefix = uniqueIdPrefix;
      Bpl.Program boogieProgram = translator.Translate(dafnyProgram);

      resolver.ReInitializeVerificationErrors(requestId, boogieProgram.TopLevelDeclarations);

      PipelineOutcome oc = BoogiePipeline(boogieProgram, requestId, er);
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
    static PipelineOutcome BoogiePipeline(Bpl.Program/*!*/ program, string requestId, ErrorReporterDelegate er)
    {
      Contract.Requires(program != null);

      PipelineOutcome oc = BoogieResolveAndTypecheck(program);
      if (oc == PipelineOutcome.ResolvedAndTypeChecked) {
        ExecutionEngine.EliminateDeadVariables(program);
        ExecutionEngine.CollectModSets(program);
        ExecutionEngine.CoalesceBlocks(program);
        ExecutionEngine.Inline(program);  
        return ExecutionEngine.InferAndVerify(program, new PipelineStatistics(), er, requestId);
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
