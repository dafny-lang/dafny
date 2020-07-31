using Microsoft.Boogie;
using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;

namespace Microsoft.Dafny.LSPServer
{

  class DiagnosticErrorReporter : ErrorReporter
  {
    Dictionary<string, List<Diagnostic>> diagnostics = new Dictionary<string, List<Diagnostic>>();

    public IReadOnlyDictionary<string, List<Diagnostic>> Diagnostics => diagnostics;

    public OutputPrinter AsBoogieOutputPrinter => new BoogieOutputPrinter(this);

    public void ReportBoogieError(ErrorInformation error)
    {
      var tok = error.Tok;
      Diagnostic item = new Diagnostic
      {
        Severity = DiagnosticSeverity.Error,
        Message = error.Msg,
        Range = new Range(new Position(tok.line, tok.col), new Position(tok.line, tok.col + 1))
      };
      AddDiagnosticForFile(item, tok.filename);
    }

    public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg)
    {
      Diagnostic item = new Diagnostic
      {
        Severity = ConvertErrorLevel(level),
        Message = msg,
        Range = new Range(new Position(tok.line, tok.col), new Position(tok.line, tok.col + 1))
      };
      string filename = tok.filename;
      AddDiagnosticForFile(item, filename);
      return true;
    }

    public void AddDiagnosticForFile(Diagnostic item, string filename)
    {
      var fileDiagnostics = diagnostics.ContainsKey(filename)
                      ? diagnostics[filename]
                      : diagnostics[filename] = new List<Diagnostic>();

      fileDiagnostics.Add(item);
    }

    static DiagnosticSeverity ConvertErrorLevel(ErrorLevel level)
    {
      switch (level)
      {
        case ErrorLevel.Error:
          return DiagnosticSeverity.Error;
        case ErrorLevel.Warning:
          return DiagnosticSeverity.Warning;
        case ErrorLevel.Info:
          return DiagnosticSeverity.Information;
      }
      throw new NotSupportedException();
    }
  }
}
