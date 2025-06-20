using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using DafnyCore;

namespace Microsoft.Dafny;

public abstract class ErrorReporter(DafnyOptions options) {
  public DafnyOptions Options { get; } = options;

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

  public bool Message(MessageSource source, ErrorLevel level, string errorId, IOrigin tok, params object[] messageParts) {
    return MessageCore(source, level, errorId, tok, messageParts);
  }

  public bool MessageCore(MessageSource source, ErrorLevel level, string errorId, IOrigin rootTok, IReadOnlyList<object> messageParts) {
    if (ErrorsOnly && level != ErrorLevel.Error) {
      return false;
    }
    var relatedInformation = new List<DafnyRelatedInformation>();

    var usingSnippets = Options.Get(Snippets.ShowSnippets);
    relatedInformation.AddRange(
      ErrorReporterExtensions.CreateDiagnosticRelatedInformationFor(rootTok, usingSnippets));

    var dafnyDiagnostic = new DafnyDiagnostic(source, errorId!, rootTok.ReportingRange, messageParts.Select(m => m.ToString()).ToArray(), level, relatedInformation);
    return MessageCore(dafnyDiagnostic);
  }

  public abstract bool MessageCore(DafnyDiagnostic dafnyDiagnostic);

  public virtual void Error(MessageSource source, string errorId, IOrigin tok, params object[] messageParts) {
    Contract.Requires(tok != null);
    Message(source, ErrorLevel.Error, errorId, tok, messageParts);
  }

  public abstract int Count(ErrorLevel level);
  public abstract int CountExceptVerifierAndCompiler(ErrorLevel level);

  // This method required by the Parser
  internal void Error(MessageSource source, Enum errorId, Uri uri, int line, int col, string msg) {
    var tok = new Token(line, col);
    tok.Uri = uri;
    Error(source, errorId, tok, msg);
  }

  public void Error(MessageSource source, Enum errorId, IOrigin tok, params string[] messageParts) {
    Contract.Requires(tok != null);
    Error(source, errorId.ToString(), tok, messageParts);
  }

  public void Error(MessageSource source, INode v, params object[] messageParts) {
    Contract.Requires(v != null);
    Error(source, (string)null, v.Origin, messageParts);
  }

  public void Error(MessageSource source, Enum errorId, INode v, params object[] messageParts) {
    Contract.Requires(v != null);
    Error(source, errorId, v.Origin, messageParts);
  }

  public void Warning(MessageSource source, Enum errorId, IOrigin tok, params object[] messageParts) {
    Contract.Requires(tok != null);
    Message(source, ErrorLevel.Warning, errorId.ToString(), tok, messageParts);
  }

  public void Deprecated(MessageSource source, string errorId, IOrigin tok, params object[] messageParts) {
    Contract.Requires(tok != null);
    if (Options.DeprecationNoise != 0) {
      Warning(source, errorId, tok, messageParts);
    } else {
      Message(source, ErrorLevel.Info, errorId, tok, messageParts);
    }
  }

  public void Deprecated(MessageSource source, Enum errorId, IOrigin tok, params object[] messageParts) {
    Contract.Requires(tok != null);
    if (Options.DeprecationNoise != 0) {
      Warning(source, errorId, tok, messageParts);
    } else {
      Contract.Requires(tok != null);
      Message(source, ErrorLevel.Info, errorId.ToString(), tok, messageParts);
    }
  }

  public void Info(MessageSource source, IOrigin tok, string format) {
    Contract.Requires(tok != null);
    Contract.Requires(format != null);
    Message(source, ErrorLevel.Info, "", tok, format);
  }

  public void Info(MessageSource source, IOrigin tok, params object[] messageParts) {
    Contract.Requires(tok != null);
    Message(source, ErrorLevel.Info, "", tok, messageParts);
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

  public void Message(MessageSource source, ErrorLevel errorLevel, IOrigin origin, params object[] messageParts) {
    Message(source, errorLevel, null, origin, messageParts);
  }

  public void Error(MessageSource source, object errorId, IOrigin origin, params object[] messageParts) {
    Message(source, ErrorLevel.Error, errorId.ToString(), origin, messageParts);
  }

  public void Error(MessageSource source, IOrigin origin, params object[] messageParts) {
    Message(source, ErrorLevel.Error, null, origin, messageParts);
  }

  public void Error(MessageSource source, object errorId, INode node, params object[] messageParts) {
    Message(source, ErrorLevel.Error, errorId.ToString(), node.Origin, messageParts);
  }

  public void Warning(MessageSource source, string errorId, IOrigin origin, params object[] messageParts) {
    Message(source, ErrorLevel.Warning, errorId, origin, messageParts);
  }

  public void Warning(MessageSource source, ResolutionErrors.ErrorId errorId, IOrigin origin, params object[] messageParts) {
    Warning(source, errorId.ToString(), origin, messageParts);
  }
}
