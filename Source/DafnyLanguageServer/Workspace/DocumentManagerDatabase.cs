using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.DependencyInjection;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of DocumentManagers
  /// </summary>
  public class DocumentManagerDatabase : IDocumentDatabase {

    private readonly IServiceProvider services;

    private VerifierOptions VerifierOptions { get; }
    private readonly DocumentOptions documentOptions;

    private readonly Dictionary<DocumentUri, DocumentManager> documents = new();

    public DocumentManagerDatabase(
      IServiceProvider services,
      DocumentOptions documentOptions,
      VerifierOptions verifierOptions) {
      this.services = services;
      this.documentOptions = documentOptions;
      VerifierOptions = verifierOptions;

      // TODO improve
      // Initialises DafnyOptions.O
      services.GetRequiredService<IDafnyParser>();

      DafnyOptions.O.ProverOptions = GetProverOptions(this.documentOptions);
    }

    private static List<string> GetProverOptions(DocumentOptions options) {
      return options.ProverOptions.Split(
        new[] { " ", "\n", "\t" },
        StringSplitOptions.RemoveEmptyEntries
      ).ToList();
    }

    public void OpenDocument(DocumentTextBuffer document) {
      documents.Add(document.Uri, new DocumentManager(services, documentOptions, VerifierOptions, document));
    }

    public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
      var documentUri = documentChange.TextDocument.Uri;
      if (!documents.TryGetValue(documentUri, out var state)) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      state.UpdateDocument(documentChange);
    }

    public void SaveDocument(TextDocumentIdentifier documentId) {
      if (!documents.TryGetValue(documentId.Uri, out var documentState)) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }

      documentState.Save();
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.Remove(documentId.Uri, out var state)) {
        await state.CloseAsync();
        return true;
      }
      return false;
    }

    public Task<DafnyDocument?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var state)) {
        return state.GetResolvedDocumentAsync();
      }
      return Task.FromResult<DafnyDocument?>(null);
    }

    public Task<DafnyDocument?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.LastDocumentAsync!;
      }
      return Task.FromResult<DafnyDocument?>(null);
    }

    public DocumentManager? GetDocumentManager(TextDocumentIdentifier documentId) {
      return documents.GetValueOrDefault(documentId.Uri);
    }

    public IEnumerable<CompilationManager> Documents => documents.Values.Select(m => m.CompilationManager);

  }
}
