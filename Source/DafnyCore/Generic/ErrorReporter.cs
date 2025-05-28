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

  public bool Message(MessageSource source, ErrorLevel level, string errorId, IOrigin tok, string formatMsg, params object[] arguments) {
    return MessageCore(source, level, errorId, tok, formatMsg, arguments);
  }

  public bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IOrigin rootTok, string formatMsg, object[] arguments) {
    if (ErrorsOnly && level != ErrorLevel.Error) {
      return false;
    }
    var relatedInformation = new List<DafnyRelatedInformation>();

    var usingSnippets = Options.Get(Snippets.ShowSnippets);
    relatedInformation.AddRange(
      ErrorReporterExtensions.CreateDiagnosticRelatedInformationFor(rootTok, usingSnippets));

    var dafnyDiagnostic = new DafnyDiagnostic(source, errorId!, rootTok.ReportingRange, formatMsg, arguments, level, relatedInformation);
    return MessageCore(dafnyDiagnostic);
  }

  public abstract bool MessageCore(DafnyDiagnostic dafnyDiagnostic);

  public virtual void Error(MessageSource source, string errorId, IOrigin tok, string formatMsg, object[] arguments) {
    Contract.Requires(tok != null);
    Message(source, ErrorLevel.Error, errorId, tok, formatMsg, arguments);
  }

  public abstract int Count(ErrorLevel level);
  public abstract int CountExceptVerifierAndCompiler(ErrorLevel level);

  // This method required by the Parser
  internal void Error(MessageSource source, Enum errorId, Uri uri, int line, int col, string msg) {
    var tok = new Token(line, col);
    tok.Uri = uri;
    Error(source, errorId, tok, msg, []);
  }

  public void Error(MessageSource source, IOrigin tok, string message) {
    Contract.Requires(tok != null);
    Error(source, null, tok, message);
  }

  public void Error(MessageSource source, Enum errorId, IOrigin tok, string formatMsg, object[] arguments) {
    Contract.Requires(tok != null);
    Error(source, errorId.ToString(), tok, formatMsg, arguments);
  }

  public void Error(MessageSource source, string errorId, Declaration d, string formatMsg, object[] arguments) {
    Contract.Requires(d != null);
    Contract.Requires(errorId != null);
    Error(source, errorId, d.Origin, formatMsg, arguments);
  }

  public void Error(MessageSource source, Enum errorId, Declaration d, string formatMsg, object[] arguments) {
    Contract.Requires(d != null);
    Error(source, errorId, d.Origin, formatMsg, arguments);
  }

  public void Error(MessageSource source, Enum errorId, Statement s, string formatMsg, object[] arguments) {
    Contract.Requires(s != null);
    Error(source, errorId, s.Origin, formatMsg, arguments);
  }

  public void Error(MessageSource source, Statement s, string format, params object[] args) {
    Contract.Requires(s != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, null, s.Origin, string.Format(format, args));
  }

  public void Error(MessageSource source, INode v, string format, params object[] args) {
    Contract.Requires(v != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, null, v.Origin, string.Format(format, args));
  }

  public void Error(MessageSource source, Enum errorId, INode v, string formatMsg, object[] arguments) {
    Contract.Requires(v != null);
    Error(source, errorId, v.Origin, formatMsg, arguments);
  }

  public void Error(MessageSource source, Enum errorId, Expression e, string formatMsg, object[] arguments) {
    Contract.Requires(e != null);
    Error(source, errorId, e.Origin, formatMsg, arguments);
  }

  public void Error(MessageSource source, Expression e, string format, params object[] args) {
    Contract.Requires(e != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Error(source, null, e.Origin, string.Format(format, args));
  }

  public void Warning(MessageSource source, Enum errorId, IOrigin tok, string formatMsg, object[] arguments) {
    Contract.Requires(tok != null);
    Message(source, ErrorLevel.Warning, errorId.ToString(), tok, formatMsg, arguments);
  }

  public void Deprecated(MessageSource source, string errorId, IOrigin tok, string formatMsg, params object[] arguments) {
    Contract.Requires(tok != null);
    if (Options.DeprecationNoise != 0) {
      Warning(source, errorId, tok, formatMsg, arguments);
    } else {
      Info(source, tok, errorId, arguments);
    }
  }

  public void Deprecated(MessageSource source, Enum errorId, IOrigin tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    if (Options.DeprecationNoise != 0) {
      Warning(source, errorId, tok, Format(format, args), []);
    } else {
      Info(source, errorId.ToString(), tok, format, args);
    }
  }

  public void Info(MessageSource source, string errorId, IOrigin tok, string formatMsg, object[] arguments) {
    Contract.Requires(tok != null);
    Message(source, ErrorLevel.Info, errorId, tok, formatMsg, arguments);
  }

  public void Info(MessageSource source, IOrigin tok, string format) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Message(source, ErrorLevel.Info, "", tok, format);
  }

  public void Info(MessageSource source, IOrigin tok, string format, params object[] args) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Contract.Requires(args != null);
    Message(source, ErrorLevel.Info, "", tok, string.Format(format, args));
  }

  private string Format(string format, object[] args) {
    // In some cases, the "format" isn't actually a (Dafny-generated) format string, but a (user-defined) literal string.
    // Such a user-defined literal may contain format information, like the "{0}" in the "ensures x in {0} <==> x in {1}".
    // To prevent such string from going to string.Format, we first check if "args" has any arguments at all.
    // This solves all known issues.
    return args.Length == 0 ? format : string.Format(format, args);
  }

  public static string FormatDiagnostic(DafnyOptions options, DafnyDiagnostic diagnostic) {
    var range = diagnostic.Range.StartToken == Token.Cli ? null : diagnostic.Range;
    return $"{range.ToFileRangeString(options)}: {diagnostic.Level.ToString()}: {diagnostic.Message}";
  }

  public void Error(MessageSource source, IOrigin origin, string formatMsg, string arguments) {
    Error(source, null, origin, string.Format(formatMsg, arguments));
  }

  public void Message(MessageSource source, ErrorLevel errorLevel, IOrigin origin, string formatMsg) {
    Message(source, errorLevel, null, origin, formatMsg, []);
  }

  //[Obsolete]
  public void Error(MessageSource source, object errorId, IOrigin origin, string formatMsg, params object[] formatArguments) {
    Message(source, ErrorLevel.Error, errorId.ToString(), origin, string.Format(formatMsg, formatArguments), []);
  }

  //[Obsolete]
  public void Error(MessageSource source, object errorId, IOrigin origin, string message) {
    Message(source, ErrorLevel.Error, errorId + "", origin, message, []);
  }

  //[Obsolete]
  // public void Message(MessageSource source, ErrorLevel level, object errorId, IOrigin origin, string message) {
  //   Message(source, level, errorId ?? "", origin, [message]);
  // }

  //[Obsolete]
  public void Error(MessageSource source, IOrigin origin, string formatMsg, params object[] formatArguments) {
    Message(source, ErrorLevel.Error, null, origin, string.Format(formatMsg, formatArguments), []);
  }

  //[Obsolete]
  public void Error(MessageSource source, object errorId, INode node, string formatMsg, params object[] formatArguments) {
    Message(source, ErrorLevel.Error, errorId.ToString(), node.Origin, string.Format(formatMsg, formatArguments), []);
  }


  //[Obsolete]
  public void Error(MessageSource source, object errorId, INode node, string message) {
    Message(source, ErrorLevel.Error, errorId.ToString(), node.Origin, message, []);
  }

  //[Obsolete]
  public void Error(MessageSource source, object errorId, INode node, string formatMsg, string formatArguments) {
    Message(source, ErrorLevel.Error, errorId.ToString(), node.Origin, string.Format(formatMsg, formatArguments), []);
  }

  public void Warning(MessageSource source, string errorId, IOrigin origin, string message) {
    Message(source, ErrorLevel.Warning, errorId, origin, message, []);
  }

  public void Warning(MessageSource source, string errorId, IOrigin origin, string formatMsg, params object[] formatArguments) {
    Message(source, ErrorLevel.Warning, errorId, origin, string.Format(formatMsg, formatArguments), []);
  }

  public void Warning(MessageSource source, ResolutionErrors.ErrorId errorId, IOrigin origin, string formatMsg) {
    Warning(source, errorId.ToString(), origin, formatMsg);
  }
}
