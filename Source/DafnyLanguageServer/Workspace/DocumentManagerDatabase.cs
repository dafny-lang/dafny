using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using Microsoft.Extensions.DependencyInjection;

using System.IO;
using System.Net.Mime;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of DocumentManagers
  /// </summary>
  public class DocumentManagerDatabase : IDocumentDatabase {

    private readonly IServiceProvider services;

    private readonly Dictionary<DocumentUri, ProjectManager> managers = new();
    private readonly LanguageServerFilesystem fileSystem;

    public DocumentManagerDatabase(IServiceProvider services) {
      this.services = services;
      this.fileSystem = services.GetRequiredService<LanguageServerFilesystem>();
    }

    public void OpenDocument(TextDocumentItem document) {
      fileSystem.OpenDocument(document);
      DafnyProject profileFile = FindProjectFile(document) ?? ImplicitProject(document);
      var existingManager = managers.GetValueOrDefault(document.Uri);

      if (existingManager != null) {
        if (!existingManager.Project.Equals(profileFile)) {
          managers[document.Uri] = new ProjectManager(services, profileFile);
        }
      } else {
        managers[document.Uri] = new ProjectManager(services, profileFile);
      }
    }

    private DafnyProject ImplicitProject(TextDocumentItem documentItem) {
      return new DafnyProject();
    }

    private DafnyProject? FindProjectFile(TextDocumentIdentifier document) {

      DafnyProject? projectFile = null;
      var uri = document.Uri;

      var folder = Path.GetDirectoryName(uri.GetFileSystemPath());
      while (!string.IsNullOrEmpty(folder)) {
        var children = Directory.GetFiles(folder, "dfyconfig.toml");
        if (children.Length > 0) {
          var errorWriter = TextWriter.Null;
          var outputWriter = TextWriter.Null;
          projectFile = DafnyProject.Open(new Uri(children[0]), outputWriter, errorWriter);
          if (projectFile != null) {
            break;
          }
        }

        folder = Path.GetDirectoryName(folder);
      }

      return projectFile;
    }

    public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
      fileSystem.UpdateDocument(documentChange);
      var documentUri = documentChange.TextDocument.Uri;
      if (!managers.TryGetValue(documentUri, out var state)) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      state.UpdateDocument(documentChange);
    }

    public void SaveDocument(TextDocumentIdentifier documentId) {
      if (!managers.TryGetValue(documentId.Uri, out var documentState)) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }

      documentState.Save(documentId);
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      fileSystem.CloseDocument(documentId);
      if (managers.Remove(documentId.Uri, out var state)) {
        await state.CloseAsync(documentId);
        return true;
      }
      return false;
    }

    public Task<IdeState?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      if (managers.TryGetValue(documentId.Uri, out var state)) {
        return state.GetSnapshotAfterResolutionAsync(documentId)!;
      }
      return Task.FromResult<IdeState?>(null);
    }

    public Task<DocumentAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      if (managers.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.GetLastDocumentAsync()!;
      }
      return Task.FromResult<DocumentAfterParsing?>(null);
    }

    public ProjectManager? GetDocumentManager(TextDocumentIdentifier documentId) {
      return managers.GetValueOrDefault(documentId.Uri);
    }

    public IEnumerable<ProjectManager> Managers => managers.Values;

  }
}
