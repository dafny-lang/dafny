using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using Microsoft.Extensions.DependencyInjection;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of DocumentManagers
  /// </summary>
  public class ProjectManagerDatabase : IProjectDatabase {
    private readonly CreateProjectManager createProjectManager;

    private readonly Dictionary<DocumentUri, ProjectManager> documents = new();
    private readonly LanguageServerFilesystem fileSystem;

    public ProjectManagerDatabase(LanguageServerFilesystem fileSystem, CreateProjectManager createProjectManager) {
      this.createProjectManager = createProjectManager;
      this.fileSystem = fileSystem;
    }

    public void OpenDocument(TextDocumentItem document) {
      var identifier = new VersionedTextDocumentIdentifier {
        Version = document.Version!.Value,
        Uri = document.Uri
      };
      fileSystem.OpenDocument(document);
      documents.Add(document.Uri, createProjectManager(identifier));
    }

    public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
      fileSystem.UpdateDocument(documentChange);
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
      fileSystem.CloseDocument(documentId);
      if (documents.Remove(documentId.Uri, out var state)) {
        await state.CloseAsync();
        return true;
      }
      return false;
    }

    public Task<IdeState?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var state)) {
        return state.GetSnapshotAfterResolutionAsync()!;
      }
      return Task.FromResult<IdeState?>(null);
    }

    public Task<CompilationAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.GetLastDocumentAsync()!;
      }
      return Task.FromResult<CompilationAfterParsing?>(null);
    }

    public ProjectManager? GetProjectManager(TextDocumentIdentifier documentId) {
      return documents.GetValueOrDefault(documentId.Uri);
    }

    public IEnumerable<ProjectManager> Managers => documents.Values;

  }
}
