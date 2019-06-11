using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.ObjectModel;
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
    readonly ITextBuffer _buffer;
    Dafny.Program _program;
    static object bufferDafnyKey = new object();

    List<DafnyError> _errors = new List<DafnyError>();
    public List<DafnyError> Errors { get { return _errors; } }

    public DafnyDriver(ITextBuffer buffer, string filename) {
      _buffer = buffer;
      _snapshot = buffer.CurrentSnapshot;
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
        options.AutoTriggers = true;
        options.ErrorTrace = 0;
        options.VcsCores = Math.Max(1, System.Environment.ProcessorCount - 1);
        options.ModelViewFile = "-";
        options.UnicodeOutput = true;
        Dafny.DafnyOptions.Install(options);

        // Read additional options from DafnyOptions.txt
        string codebase = Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location);
        string optionsFilePath = Path.Combine(codebase, "DafnyOptions.txt");
        if (File.Exists(optionsFilePath)) {
          var optionsReader = new StreamReader(new FileStream(optionsFilePath, FileMode.Open, FileAccess.Read));
          List<string> args = new List<string>();
          while (true) {
            string line = optionsReader.ReadLine();
            if (line == null) break;
            line = line.Trim();
            if (line.Length == 0 || line.StartsWith("//")) continue;
            args.Add(line);
          }
          optionsReader.Close();
          CommandLineOptions.Clo.Parse(args.ToArray());
        } else {
          options.ApplyDefaultOptions();
        }

        ExecutionEngine.printer = new DummyPrinter();
        ExecutionEngine.errorInformationFactory = new DafnyErrorInformationFactory();
        ChangeIncrementalVerification(2);
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

    internal Dafny.Program ProcessResolution(bool runResolver) {
      if (!ParseAndTypeCheck(runResolver)) {
        return null;
      }
      return _program;
    }

    bool ParseAndTypeCheck(bool runResolver) {
      Tuple<ITextSnapshot, Dafny.Program, List<DafnyError>> parseResult;
      Dafny.Program program;
      var errorReporter = new VSErrorReporter(this);
      if (_buffer.Properties.TryGetProperty(bufferDafnyKey, out parseResult) &&
         (parseResult.Item1 == _snapshot)) {
        // already parsed;
        program = parseResult.Item2;
        _errors = parseResult.Item3;
        if (program == null)
          runResolver = false;
      } else {
        Dafny.ModuleDecl module = new Dafny.LiteralModuleDecl(new Dafny.DefaultModuleDecl(), null);
        Dafny.BuiltIns builtIns = new Dafny.BuiltIns();
        var parseErrors = new Dafny.Errors(errorReporter);
        int errorCount = Dafny.Parser.Parse(_snapshot.GetText(), _filename, _filename, null, module, builtIns, parseErrors);
        string errString = Dafny.Main.ParseIncludes(module, builtIns, new List<string>(), parseErrors);

        if (errorCount != 0 || errString != null) {
          runResolver = false;
          program = null;
        } else {
          program = new Dafny.Program(_filename, module, builtIns, errorReporter);
        }
        _buffer.Properties[bufferDafnyKey] = new Tuple<ITextSnapshot, Dafny.Program, List<DafnyError>>(_snapshot, program, _errors);
      }
      if (!runResolver) {
        return false;
      }

      var r = new Resolver(program);
      r.ResolveProgram(program);
      if (errorReporter.Count(ErrorLevel.Error) != 0)
        return false;

      _program = program;
      return true;  // success
    }


    void RecordError(string filename, int line, int col, ErrorCategory cat, string msg, bool isRecycled = false)
    {
      _errors.Add(new DafnyError(filename, line - 1, col - 1, cat, msg, _snapshot, isRecycled, null, System.IO.Path.GetFullPath(this._filename) == filename));
    }

    class VSErrorReporter : Dafny.ErrorReporter
    {
      DafnyDriver dd;

      public VSErrorReporter(DafnyDriver dd) {
        this.dd = dd;
      }

      // TODO: The error tracking could be made better to track the full information returned by Dafny
      public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
        if (base.Message(source, level, tok, msg)) {
          switch (level) {
            case ErrorLevel.Error:
              dd.RecordError(tok.filename, tok.line, tok.col, source == MessageSource.Parser ? ErrorCategory.ParseError : ErrorCategory.ResolveError, msg);
              break;
            case ErrorLevel.Warning:
              dd.RecordError(tok.filename, tok.line, tok.col, source == MessageSource.Parser ? ErrorCategory.ParseWarning : ErrorCategory.ResolveWarning, msg);
              break;
            case ErrorLevel.Info:
              // The AllMessages variable already keeps track of this
              break;
          }
          return true;
        } else {
          return false;
        }
      }
    }

    public class ErrorSink : Bpl.IErrorSink
    {
      DafnyDriver dd;

      public ErrorSink(DafnyDriver dd) {
        this.dd = dd;
      }
      public void Error(Bpl.IToken tok, string msg) {
        dd.RecordError(tok.filename, tok.line, tok.col, ErrorCategory.VerificationError, msg);
      }
    }

    #endregion

    #region Compilation

    public static void Compile(Dafny.Program dafnyProgram, TextWriter outputWriter)
    {
      Microsoft.Dafny.DafnyOptions.O.SpillTargetCode = 1;
      // Currently there are no provisions for specifying other files to compile with from the
      // VS interface, so just send an empty list.
      ReadOnlyCollection<string> otherFileNames = new List<string>().AsReadOnly();
      Microsoft.Dafny.DafnyDriver.CompileDafnyProgram(dafnyProgram, dafnyProgram.FullName, otherFileNames, true, outputWriter);
    }

    #endregion

    #region Boogie interaction

    class DafnyErrorInformationFactory : ErrorInformationFactory
    {
      public override ErrorInformation CreateErrorInformation(IToken tok, string msg, string requestId, string originalRequestId, string category = null)
      {
        return new DafnyErrorInformation(tok, msg, requestId, originalRequestId, category);
      }
    }

    class DafnyErrorInformation : ErrorInformation
    {
      public DafnyErrorInformation(IToken tok, string msg, string requestId, string originalRequestId, string category = null)
        : base(tok, msg)
      {
        RequestId = requestId;
        OriginalRequestId = originalRequestId;
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

    public static int IncrementalVerificationMode()
    {
      return Dafny.DafnyOptions.Clo.VerifySnapshots;
    }

    public static void SetDiagnoseTimeouts(bool v)
    {
      Dafny.DafnyOptions.Clo.RunDiagnosticsOnTimeout = v;
    }

    public static int ChangeIncrementalVerification(int mode)
    {
      var old = Dafny.DafnyOptions.Clo.VerifySnapshots;
      if (mode == 1 && 1 <= old)
      {
        // Disable mode 1.
        Dafny.DafnyOptions.Clo.VerifySnapshots = 0;
      }
      else if (mode == 2 && old == 2)
      {
        // Disable mode 2.
        Dafny.DafnyOptions.Clo.VerifySnapshots = 1;
      }
      else
      {
        // Enable mode.
        Dafny.DafnyOptions.Clo.VerifySnapshots = mode;
      }
      return Dafny.DafnyOptions.Clo.VerifySnapshots;
    }

    public static bool ChangeAutomaticInduction() {
      var old = Dafny.DafnyOptions.O.Induction;
      // toggle between modes 1 and 3
      Dafny.DafnyOptions.O.Induction = old == 1 ? 3 : 1;
      return Dafny.DafnyOptions.O.Induction == 3;
    }

    public bool Verify(Dafny.Program dafnyProgram, ResolverTagger resolver, string uniqueIdPrefix, string requestId, ErrorReporterDelegate er) {

      Dafny.Translator translator = new Dafny.Translator(dafnyProgram.reporter);
      var translatorFlags = new Dafny.Translator.TranslatorFlags() { InsertChecksums = true, UniqueIdPrefix = uniqueIdPrefix };


      var boogiePrograms = Dafny.Translator.Translate(dafnyProgram, dafnyProgram.reporter, translatorFlags);

      var impls = boogiePrograms.SelectMany(p => p.Item2.Implementations);
      resolver.ReInitializeVerificationErrors(requestId, impls);

      bool success = false;
      var errorSink = new ErrorSink(this);

      foreach (var kv in boogiePrograms) {
        var boogieProgram = kv.Item2;

        // TODO(wuestholz): Maybe we should use a fixed program ID to limit the memory overhead due to the program cache in Boogie.
        PipelineOutcome oc = BoogiePipeline(boogieProgram, 1 < Dafny.DafnyOptions.Clo.VerifySnapshots ? uniqueIdPrefix : null, requestId, errorSink, er);
        switch (oc) {
          case PipelineOutcome.Done:
          case PipelineOutcome.VerificationCompleted:
            // TODO:  This would be the place to proceed to compile the program, if desired
            success = true;
            break;
          case PipelineOutcome.FatalError:
          default:
            return false;
        }
      }
      return success;
    }

    /// <summary>
    /// Resolve, type check, infer invariants for, and verify the given Boogie program.
    /// The intention is that this Boogie program has been produced by translation from something
    /// else.  Hence, any resolution errors and type checking errors are due to errors in
    /// the translation.
    /// </summary>
    static PipelineOutcome BoogiePipeline(Bpl.Program/*!*/ program, string programId, string requestId, ErrorSink errorSink, ErrorReporterDelegate er)
    {
      Contract.Requires(program != null);

      PipelineOutcome oc = BoogieResolveAndTypecheck(program, errorSink);
      if (oc == PipelineOutcome.ResolvedAndTypeChecked) {
        ExecutionEngine.EliminateDeadVariables(program);
        ExecutionEngine.CollectModSets(program);
        ExecutionEngine.CoalesceBlocks(program);
        ExecutionEngine.Inline(program);
        return ExecutionEngine.InferAndVerify(program, new PipelineStatistics(), programId, er, requestId);
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
    static PipelineOutcome BoogieResolveAndTypecheck(Bpl.Program program, ErrorSink errorSink) {
      Contract.Requires(program != null);
      // ---------- Resolve ------------------------------------------------------------
      int errorCount = program.Resolve(errorSink);
      if (errorCount != 0) {
        return PipelineOutcome.ResolutionError;
      }

      // ---------- Type check ------------------------------------------------------------
      errorCount = program.Typecheck(errorSink);
      if (errorCount != 0) {
        return PipelineOutcome.TypeCheckingError;
      }

      return PipelineOutcome.ResolvedAndTypeChecked;
    }

    #endregion
  }

}
