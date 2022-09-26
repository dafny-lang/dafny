using Microsoft.Dafny.LanguageServer.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  public class TextChangeProcessor : ITextChangeProcessor {
    public DocumentTextBuffer ApplyChange(DocumentTextBuffer originalTextDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var newBuffer = ApplyTextChanges(originalTextDocument.Buffer, documentChange.ContentChanges, cancellationToken);
      return new DocumentTextBuffer(new TextDocumentItem {
        Version = documentChange.TextDocument.Version,
        Uri = originalTextDocument.Uri,
        Text = newBuffer.Text
      }, newBuffer);
    }

    private static TextBuffer ApplyTextChanges(TextBuffer buffer, Container<TextDocumentContentChangeEvent> changes, CancellationToken cancellationToken) {
      var mergedBuffer = buffer;
      foreach (var change in changes) {
        cancellationToken.ThrowIfCancellationRequested();
        mergedBuffer = mergedBuffer.ApplyTextChange(change);
      }
      return mergedBuffer;
    }
  }
}
