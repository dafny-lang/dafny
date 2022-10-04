using System.Net.Mime;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class DocumentTextBuffer {
  public TextDocumentItem TextDocumentItem { get; }
  public TextBuffer Buffer { get; }
  public DocumentTextBuffer(TextDocumentItem documentItem) {
    TextDocumentItem = documentItem;
    Buffer = new TextBuffer(documentItem.Text);
  }

  public DocumentTextBuffer(TextDocumentItem documentItem, TextBuffer buffer) {
    TextDocumentItem = documentItem;
    Buffer = buffer;
  }

  public Position FromIndex(int index) {
    return Buffer.FromIndex(index);
  }

  public int ToIndex(Position position) {
    return Buffer.ToIndex(position);
  }

  public string Extract(Range range) {
    return Buffer.Extract(range);
  }

  public static implicit operator TextDocumentItem(DocumentTextBuffer buffer) => buffer.TextDocumentItem;
  public string Text => TextDocumentItem.Text;
  public DocumentUri Uri => TextDocumentItem.Uri;
  public int? Version => TextDocumentItem.Version;

  public int NumberOfLines => Buffer.Lines.Count;
}