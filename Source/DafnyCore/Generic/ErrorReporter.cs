using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using DafnyCore;

namespace Microsoft.Dafny;

public abstract class ErrorReporter {
  public DafnyOptions Options { get; }

  protected ErrorReporter(DafnyOptions options) {
    this.Options = options;
  }

  public bool ErrorsOnly { get; set; }

  public bool FailCompilation => FailCompilationMessage != null;

  public string FailCompilationMessage {
    get {
      if (HasErrors) {
        return "errors were found";
      }

      if (WarningCount > 0 && Options.FailOnWarnings) {
        return "warnings were found and --allow-warnings was not specified";
      }
      return null;
    }
  }

  public int ErrorCount => Count(ErrorLevel.Error);

  public bool HasErrors => ErrorCount > 0;
  public int WarningCount => Count(ErrorLevel.Warning);

  public int ErrorCountUntilResolver => CountExceptVerifierAndCompiler(ErrorLevel.Error);

  public bool Message(MessageSource source, ErrorLevel level, string errorId, IOrigin tok, string msg) {
    return MessageCore(source, level, errorId, tok, msg);
  }

  public bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IOrigin rootTok, string msg) {
    if (ErrorsOnly && level != ErrorLevel.Error) {
      return false;
    }
    var relatedInformation = new List<DafnyRelatedInformation>();

    var usingSnippets = Options.Get(Snippets.ShowSnippets);
    relatedInformation.AddRange(
      ErrorReporterExtensions.CreateDiagnosticRelatedInformationFor(rootTok, usingSnippets));

    var dafnyDiagnostic = new DafnyDiagnostic(source, errorId!, rootTok.ReportingRange, msg, level, relatedInformation);
    return MessageCore(dafnyDiagnostic);
  }

  public abstract bool MessageCore(DafnyDiagnostic dafnyDiagnostic);

  public void Error(MessageSource source, IOrigin tok, string msg) {
    Error(source, ParseErrors.ErrorId.none, tok, msg);
  }
  public virtual void Error(MessageSource source, string errorId, IOrigin tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Message(source, ErrorLevel.Error, errorId, tok, msg);
  }

  public abstract int Count(ErrorLevel level);
  public abstract int CountExceptVerifierAndCompiler(ErrorLevel level);

  // This method required by the Parser
  internal void Error(MessageSource source, Enum errorId, Uri uri, int line, int col, string msg) {
    var tok = new Token(line, col);
    tok.Uri = uri;
    Error(source, errorId, tok, msg);
  }

  public void Error(MessageSource source, IOrigin tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, tok, format, args);
  }

  public void Error(MessageSource source, Enum errorId, IOrigin tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, errorId.ToString(), tok, Format(format, args));
  }

  public void Error(MessageSource source, Enum errorId, IOrigin tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Error(source, errorId.ToString(), tok, msg);
  }

  public void Error(MessageSource source, Declaration d, string format, params object[] args) {
    Contract.Requires(d != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, d.Origin, format, args);
  }

  public void Error(MessageSource source, Enum errorId, Declaration d, string msg, params object[] args) {
    Contract.Requires(d != null);
    Contract.Requires(msg != null);
    Contract.Requires(args != null);
    Error(source, errorId, d.Origin, msg, args);
  }

  public void Error(MessageSource source, Enum errorId, Statement s, string format, params object[] args) {
    Contract.Requires(s != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, errorId, s.Origin, format, args);
  }

  public void Error(MessageSource source, Statement s, string format, params object[] args) {
    Contract.Requires(s != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, s.Origin, format, args);
  }

  public void Error(MessageSource source, INode v, string format, params object[] args) {
    Contract.Requires(v != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, v.Origin, format, args);
  }

  public void Error(MessageSource source, Enum errorId, INode v, string format, params object[] args) {
    Contract.Requires(v != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, errorId, v.Origin, format, args);
  }

  public void Error(MessageSource source, Enum errorId, Expression e, string format, params object[] args) {
    Contract.Requires(e != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, errorId, e.Origin, format, args);
  }

  public void Error(MessageSource source, Expression e, string format, params object[] args) {
    Contract.Requires(e != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, ParseErrors.ErrorId.none, e.Origin, format, args);
  }

  public void Warning(MessageSource source, Enum errorId, IOrigin tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Warning(source, errorId, tok, Format(format, args));
  }

  public void Warning(MessageSource source, Enum errorId, IOrigin tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Message(source, ErrorLevel.Warning, errorId.ToString(), tok, msg);
  }

  public void Warning(MessageSource source, string errorId, IOrigin tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Message(source, ErrorLevel.Warning, errorId, tok, msg);
  }

  public void Deprecated(MessageSource source, string errorId, IOrigin tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    if (Options.DeprecationNoise != 0) {
      Warning(source, errorId, tok, msg);
    } else {
      Info(source, tok, msg, errorId);
    }
  }

  public void Deprecated(MessageSource source, Enum errorId, IOrigin tok, string msg) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    if (Options.DeprecationNoise != 0) {
      Warning(source, errorId, tok, msg);
    } else {
      Info(source, tok, msg, errorId);
    }
  }

  public void Deprecated(MessageSource source, Enum errorId, IOrigin tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    if (Options.DeprecationNoise != 0) {
      Warning(source, errorId, tok, Format(format, args));
    }
  }

  public void Info(MessageSource source, IOrigin tok, string msg, object errorId = null) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Message(source, ErrorLevel.Info, errorId?.ToString(), tok, msg);
  }

  public void Info(MessageSource source, IOrigin tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Info(source, tok, Format(format, args));
  }

  private string Format(string format, object[] args) {
    // In some cases, the "format" isn't actually a (Dafny-generated) format string, but a (user-defined) literal string.
    // Such a user-defined literal may contain format information, like the "{0}" in the "ensures x in {0} <==> x in {1}".
    // To prevent such string from going to string.Format, we first check if "args" has any arguments at all.
    // This solves all known issues.
    return args.Length == 0 ? format : string.Format(format, args);
  }

  public string FormatDiagnostic(DafnyDiagnostic diagnostic) {
    var range = diagnostic.Range.StartToken == Token.Cli ? null : diagnostic.Range;
    return $"{range.ToFileRangeString(Options)}: {diagnostic.Level.ToString()}: {diagnostic.Message}";
  }
}
