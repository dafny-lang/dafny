using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.IO;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of DocumentManagers
  /// </summary>
  public class DocumentManagerDatabase : IDocumentDatabase {

    private readonly IServiceProvider services;

    private readonly Dictionary<DocumentUri, IProjectManager> documents = new();

    public DocumentManagerDatabase(IServiceProvider services) {
      this.services = services;
    }

    public void OpenDocument(DocumentTextBuffer document) {
      var profileFile = FindProjectFile(document);
      IProjectManager? existingManager = documents.GetValueOrDefault(document.Uri);

      IProjectManager CreateManager() {
        if (profileFile == null) {
          return new ImplicitProject(services, document);
        }

        return new ExplicitProject(services, profileFile);
      }
      
      if (existingManager != null) {
        var expectedType = profileFile == null ? typeof(ImplicitProject) : typeof(ExplicitProject);
        if (expectedType != existingManager.GetType()) {
          documents[document.Uri] = CreateManager();
        }
      } else {
        documents[document.Uri] = CreateManager();
      }

      documents[document.Uri].OpenDocument(document);
    }

    private ProjectFile? FindProjectFile(TextDocumentIdentifier document) {
      
      ProjectFile? projectFile = null;
      var uri = document.Uri;

      var folder = Path.GetDirectoryName(uri.GetFileSystemPath());
      while (!string.IsNullOrEmpty(folder)) {
        var children = Directory.GetFiles(folder, "dfyconfig.toml");
        if (children.Length > 0) {
          var errorWriter = TextWriter.Null;
          projectFile = ProjectFile.Open(new Uri(children[0]), errorWriter);
          if (projectFile != null) {
            break;
          }
        }
        folder = Path.GetDirectoryName(folder);
      }

      return projectFile;
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

      documentState.Save(documentId);
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.Remove(documentId.Uri, out var state)) {
        await state.CloseAsync(documentId);
        return true;
      }
      return false;
    }

    public Task<IdeState?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var state)) {
        return state.GetSnapshotAfterResolutionAsync(documentId)!;
      }
      return Task.FromResult<IdeState?>(null);
    }

    public Task<DocumentAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.GetLastDocumentAsync()!;
      }
      return Task.FromResult<DocumentAfterParsing?>(null);
    }

    public IProjectManager? GetDocumentManager(TextDocumentIdentifier documentId) {
      return documents.GetValueOrDefault(documentId.Uri);
    }

    public IEnumerable<IProjectManager> Documents => documents.Values;

  }
}
