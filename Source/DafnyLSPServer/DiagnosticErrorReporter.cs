using Microsoft.Boogie;
using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.IO;

namespace Microsoft.Dafny.LSPServer
{
  static class PositionUtility
  {
    public static Range ToSingleLengthRange(this Position position)
    {
      return new Range(position, new Position(position.Line, position.Character));
    }

  }

  class BoogieOutputPrinter : OutputPrinter
  {
    readonly DiagnosticErrorReporter parent;

    public BoogieOutputPrinter(DiagnosticErrorReporter parent)
    {
      this.parent = parent;
    }

    private Position BoogieToLspPosition(IToken token)
    {
      return new Position(token.line, token.col - 1);
    }

    public void ReportBplError(IToken token, string message, bool error, TextWriter tw, string category = null)
    {
      var item = new Diagnostic
      {
        Severity = error ? DiagnosticSeverity.Error : DiagnosticSeverity.Information,
        Message = message,
        // Dafny has 0-indexed columns, but Boogie counts from 1
        Range = BoogieToLspPosition(token).ToSingleLengthRange()
      };

      if (token is NestedToken nestedToken)
      {
        var relatedInformation = new List<DiagnosticRelatedInformation>();
        item.RelatedInformation = relatedInformation;
        relatedInformation.Add(new DiagnosticRelatedInformation()
        {
          Message = "Related location",
          Location = new Location()
          {
            Range = BoogieToLspPosition(nestedToken.Inner).ToSingleLengthRange(),
            Uri = nestedToken.Inner.filename
          }
        });
      }

      parent.AddDiagnosticForFile(item, token.filename);
    }

    public void ErrorWriteLine(TextWriter tw, string s)
    {
      throw new NotImplementedException();
    }

    public void ErrorWriteLine(TextWriter tw, string format, params object[] args)
    {
      throw new NotImplementedException();
    }

    public void AdvisoryWriteLine(string format, params object[] args)
    {
      throw new NotImplementedException();
    }

    public void Inform(string s, TextWriter tw)
    {
      throw new NotImplementedException();
    }

    public void WriteTrailer(PipelineStatistics stats)
    {
      throw new NotImplementedException();
    }

    public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace = true)
    {
      throw new NotImplementedException();
    }
  }

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
