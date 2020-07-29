using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LSPServer
{
    class TextDocumentManager
    {
        readonly Dictionary<DocumentUri, TextDocument> Documents = new Dictionary<DocumentUri, TextDocument>();

        public void Open(DidOpenTextDocumentParams didOpenParams)
        {
            Documents.Add(didOpenParams.TextDocument.Uri, new TextDocument(didOpenParams.TextDocument.Text));
        }

        public void Change(DidChangeTextDocumentParams didChangeParams)
        {
            if (didChangeParams.ContentChanges == null || !didChangeParams.ContentChanges.Any())
                return;

            var document = GetDocument(didChangeParams.TextDocument.Uri);
            var changes = didChangeParams.ContentChanges.ToList();
            if (changes.Count > 1)
            {
                throw new Exception("More than one document content change not supported.");
            }
            else
            {
                var change = changes[0];
                document.Text = change.Text;
            }
        }

        public void Close(DidCloseTextDocumentParams didCloseParams)
        {
            Documents.Remove(didCloseParams.TextDocument.Uri);
        }

        public TextDocument GetDocument(DocumentUri uri)
        {
            return Documents[uri];
        }
    }
}
