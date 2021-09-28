using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Util;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Language {
  public class DiagnosticErrorReporter : ErrorReporter {
    private const MessageSource verifierMessageSource = MessageSource.Other;
    private const string RelatedLocationCategory = "Related location";
    private const string RelatedLocationMessage = RelatedLocationCategory;

    private readonly DocumentUri entryDocumentUri;
    private readonly Dictionary<DocumentUri, List<Diagnostic>> diagnostics = new();
    private readonly Dictionary<DiagnosticSeverity, int> counts = new();

    public IReadOnlyDictionary<DocumentUri, List<Diagnostic>> Diagnostics => diagnostics;

    /// <summary>
    /// Creates a new instance with the given uri of the entry document.
    /// </summary>
    /// <param name="entryDocumentUri">The entry document's uri.</param>
    /// <remarks>
    /// The uri of the entry document is necessary to report general compiler errors as part of this document.
    /// </remarks>
    public DiagnosticErrorReporter(DocumentUri entryDocumentUri) {
      this.entryDocumentUri = entryDocumentUri;
    }

    public void ReportBoogieError(ErrorInformation error) {
      var relatedInformation = new List<DiagnosticRelatedInformation>();
      foreach (var auxiliaryInformation in error.Aux) {
        if (auxiliaryInformation.Category == RelatedLocationCategory) {
          relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(auxiliaryInformation.Msg, auxiliaryInformation.Tok));
        } else {
          // The execution trace is an additional auxiliary which identifies itself with
          // line=0 and character=0. These positions cause errors when exposing them, Furthermore,
          // the execution trace message appears to not have any interesting information.
          if (auxiliaryInformation.Tok.line > 0) {
            Info(verifierMessageSource, auxiliaryInformation.Tok, auxiliaryInformation.Msg);
          }
        }
      }
      AddDiagnosticForFile(
        new Diagnostic {
          Severity = DiagnosticSeverity.Error,
          Message = error.Msg,
          Range = error.Tok.GetLspRange(),
          RelatedInformation = relatedInformation,
          Source = verifierMessageSource.ToString()
        },
        GetDocumentUriOrDefault(error.Tok)
      );
    }

    private static IEnumerable<DiagnosticRelatedInformation> CreateDiagnosticRelatedInformationFor(string message, IToken token) {
      yield return new DiagnosticRelatedInformation {
        Message = message,
        Location = CreateLocation(token)
      };
      if (token is NestedToken nestedToken) {
        foreach (var nestedInformation in CreateDiagnosticRelatedInformationFor(RelatedLocationMessage, nestedToken.Inner)) {
          yield return nestedInformation;
        }
      }
    }

    private static Location CreateLocation(IToken token) {
      return new Location {
        Range = token.GetLspRange(),

        // During parsing, we store absolute paths to make reconstructing the Uri easier
        // https://github.com/dafny-lang/dafny/blob/06b498ee73c74660c61042bb752207df13930376/Source/DafnyLanguageServer/Language/DafnyLangParser.cs#L59 
        Uri = token.GetDocumentUri()
      };
    }

    public override bool Message(MessageSource source, ErrorLevel level, IToken tok, string msg) {
      if (ErrorsOnly && level != ErrorLevel.Error) {
        return false;
      }

      var item = new Diagnostic {
        Severity = ToSeverity(level),
        Message = msg,
        Range = tok.GetLspRange(),
        Source = source.ToString()
      };
      AddDiagnosticForFile(item, GetDocumentUriOrDefault(tok));
      return true;
    }

    public override int Count(ErrorLevel level) {
      if (counts.TryGetValue(ToSeverity(level), out var count)) {
        return count;
      }
      return 0;
    }

    private void AddDiagnosticForFile(Diagnostic item, DocumentUri documentUri) {
      var fileDiagnostics = diagnostics.GetOrCreate(documentUri, () => new List<Diagnostic>());

      var severity = item.Severity!.Value; // All our diagnostics have a severity.
      counts.TryGetValue(severity, out var count);
      counts[severity] = count + 1;
      fileDiagnostics.Add(item);
    }

    private DocumentUri GetDocumentUriOrDefault(IToken token) {
      return token.filename == null
        ? entryDocumentUri
        : token.GetDocumentUri();
    }

    private static DiagnosticSeverity ToSeverity(ErrorLevel level) {
      return level switch {
        ErrorLevel.Error => DiagnosticSeverity.Error,
        ErrorLevel.Warning => DiagnosticSeverity.Warning,
        ErrorLevel.Info => DiagnosticSeverity.Hint,
        _ => throw new ArgumentException($"unknown error level {level}", nameof(level))
      };
    }
  }
}