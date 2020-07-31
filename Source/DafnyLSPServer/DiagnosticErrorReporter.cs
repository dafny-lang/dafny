using Microsoft.Boogie;
using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LSPServer
{

  class DiagnosticErrorReporter : ErrorReporter
  {
    readonly Dictionary<string, List<Diagnostic>> diagnostics = new Dictionary<string, List<Diagnostic>>();
    readonly DafnyLSPServer server;

    public DiagnosticErrorReporter(DafnyLSPServer server)
    {
      this.server = server;
    }

    public IReadOnlyDictionary<string, List<Diagnostic>> Diagnostics => diagnostics;

    public OutputPrinter AsBoogieOutputPrinter => new BoogieOutputPrinter(this);

    public void ReportBoogieError(ErrorInformation error)
    {
      var tok = error.Tok;
      Diagnostic item = new Diagnostic
      {
        Severity = DiagnosticSeverity.Error,
        Message = error.Msg,
        Range = tok.BoogieToLspPosition().ToSingleLengthRange()
      };
      var relatedInformation = new List<DiagnosticRelatedInformation>();
      item.RelatedInformation = relatedInformation;
      foreach (var relatedLocation in error.Aux.Where(e => e.Category == "Related location"))
      {
        relatedInformation.Add(new DiagnosticRelatedInformation()
        {
          Message = relatedLocation.Msg,
          Location = new Location()
          {
            Range = relatedLocation.Tok.BoogieToLspPosition().ToSingleLengthRange(),
            Uri = server.FindUriFromFileName(relatedLocation.Tok.filename)
          }
        });
      }
      AddDiagnosticForFile(item, tok.filename);
    }

    public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg)
    {
      Diagnostic item = new Diagnostic
      {
        Severity = ConvertErrorLevel(level),
        Message = msg,
        Range = new Position(tok.line - 1, tok.col -1).ToSingleLengthRange()
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
