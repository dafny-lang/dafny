using Microsoft.Dafny.LanguageServer.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  public class TextChangeProcessor : ITextChangeProcessor {
    public TextDocumentItem ApplyChange(TextDocumentItem originalTextDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      return originalTextDocument with {
        Version = documentChange.TextDocument.Version,
        Text = ApplyTextChanges(originalTextDocument.Text, documentChange.ContentChanges, cancellationToken)
      };
    }

    private static string ApplyTextChanges(string originalText, Container<TextDocumentContentChangeEvent> changes, CancellationToken cancellationToken) {
      var mergedText = originalText;
      foreach (var change in changes) {
        cancellationToken.ThrowIfCancellationRequested();
        mergedText = ApplyTextChange(mergedText, change, cancellationToken);
      }
      return mergedText;
    }

    private static string ApplyTextChange(string text, TextDocumentContentChangeEvent change, CancellationToken cancellationToken) {
      if (change.Range == null) {
        // https://microsoft.github.io/language-server-protocol/specifications/specification-3-17/#textDocumentContentChangeEvent
        return change.Text;
      }
      int absoluteStart = change.Range.Start.ToAbsolutePosition(text, cancellationToken);
      int absoluteEnd = change.Range.End.ToAbsolutePosition(text, cancellationToken);
      return text[..absoluteStart] + change.Text + text[absoluteEnd..];
    }
  }
}
