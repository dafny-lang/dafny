using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Language
{
  public class DiagnosticErrorReporter : ErrorReporter
  {
    private const MessageSource verifierMessageSource = MessageSource.Other;
    private readonly Dictionary<string, List<Diagnostic>> diagnostics = new();
    private readonly Dictionary<DiagnosticSeverity, int> counts = new();

    public IReadOnlyDictionary<string, List<Diagnostic>> Diagnostics => diagnostics;

    public void ReportBoogieError(ErrorInformation error)
    {
      var tok = error.Tok;
      var relatedInformation = new List<DiagnosticRelatedInformation>() { };
      foreach (var auxErrorInfo in error.Aux)
      {
        if (auxErrorInfo.Category == "Related location") {
          relatedInformation.Add(new DiagnosticRelatedInformation()
          {
            Message = auxErrorInfo.Msg,
            Location = new Location()
            {
              Range = auxErrorInfo.Tok.GetLspRange(),
              
              // https://github.com/dafny-lang/dafny/blob/06b498ee73c74660c61042bb752207df13930376/Source/DafnyLanguageServer/Language/DafnyLangParser.cs#L59
              Uri = DocumentUri.FromFileSystemPath(auxErrorInfo.Tok.filename)
            }
          });
        } else {
          // The execution trace is an additional auxiliary which identifies itself with
          // line=0 and character=0. These positions cause errors when exposing them, Furthermore,
          // the execution trace message appears to not have any interesting information.
          if(auxErrorInfo.Tok.line > 0) {
            Info(verifierMessageSource, auxErrorInfo.Tok, auxErrorInfo.Msg);
          }
          
        }
      }
      var item = new Diagnostic
      {
        Severity = DiagnosticSeverity.Error,
        Message = error.Msg,
        Range = tok.GetLspRange(),
        RelatedInformation = relatedInformation,
        Source = verifierMessageSource.ToString()
      };
      AddDiagnosticForFile(item, tok.filename);
    }

    public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg)
    {
      if (ErrorsOnly && level != ErrorLevel.Error) {
        return false;
      }
      
      var item = new Diagnostic
      {
        Severity = ToSeverity(level),
        Message = msg,
        Range = tok.GetLspRange(),
        Source = source.ToString()
      };
      string filename = tok.filename;
      AddDiagnosticForFile(item, filename);
      return true;
    }

    public override int Count(ErrorLevel level) {
      if (counts.TryGetValue(ToSeverity(level), out var count)) {
        return count;
      }

      return 0;
    }

    private void AddDiagnosticForFile(Diagnostic item, string filename)
    {
      var fileDiagnostics = diagnostics.ContainsKey(filename)
                      ? diagnostics[filename]
                      : diagnostics[filename] = new List<Diagnostic>();

      counts.TryGetValue(item.Severity!.Value, out var count);
      counts[item.Severity!.Value] = count + 1;
      fileDiagnostics.Add(item);
    }

    private static DiagnosticSeverity ToSeverity(ErrorLevel level) {
      return level switch {
        ErrorLevel.Error => DiagnosticSeverity.Error,
        ErrorLevel.Warning => DiagnosticSeverity.Warning,
        ErrorLevel.Info => DiagnosticSeverity.Information,
        _ => throw new ArgumentException($"unknown error level {level}", nameof(level))
      };
    }
  }
}