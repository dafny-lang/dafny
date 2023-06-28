using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using Microsoft.Extensions.DependencyInjection;

using System.IO;
using System.Net.Mime;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of DocumentManagers
  /// </summary>
  public class ProjectManagerDatabase : IProjectDatabase {

    private readonly IServiceProvider services;

    private readonly Dictionary<DocumentUri, ProjectManager> managersByFile = new();
    private readonly Dictionary<DocumentUri, ProjectManager> managersByProject = new();
    private readonly LanguageServerFilesystem fileSystem;
    private VerificationResultCache verificationCache = new();

    public ProjectManagerDatabase(IServiceProvider services) {
      this.services = services;
      this.fileSystem = services.GetRequiredService<LanguageServerFilesystem>();
    }

    public void OpenDocument(TextDocumentItem document) {
      fileSystem.OpenDocument(document);
      DafnyProject profileFile = FindProjectFile(document) ?? ImplicitProject(document);
      ProjectManager? projectManager = managersByProject.GetValueOrDefault(profileFile.Uri);

      if (projectManager != null) {
        // TODO add tests for this not equals path.
        if (!projectManager.Project.Equals(profileFile)) {
          projectManager = new ProjectManager(services, verificationCache, profileFile);
        }
      } else {
        projectManager = new ProjectManager(services, verificationCache, profileFile);
      }

      managersByFile[document.Uri] = managersByProject[profileFile.Uri] = projectManager;
      projectManager.OpenDocument(document);
    }

    public static DafnyProject ImplicitProject(TextDocumentIdentifier documentItem) {
      var implicitProject = new DafnyProject {
        Includes = Array.Empty<string>(),
        Uri = documentItem.Uri.ToUri(),
        UnsavedRootFile = documentItem.Uri.ToUri()
      };
      return implicitProject;
    }

    // TODO add temporal caching
    private DafnyProject? FindProjectFile(TextDocumentIdentifier document) {

      DafnyProject? projectFile = null;
      var uri = document.Uri;

      var folder = Path.GetDirectoryName(uri.GetFileSystemPath());
      while (!string.IsNullOrEmpty(folder)) {
        var configFileUri = new Uri(Path.Combine(folder, "dfyconfig.toml"));
        if (fileSystem.Exists(configFileUri)) {
          var errorWriter = TextWriter.Null;
          var outputWriter = TextWriter.Null;
          projectFile = DafnyProject.Open(fileSystem, configFileUri, outputWriter, errorWriter);
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
      if (!managersByFile.TryGetValue(documentUri, out var state)) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      state.UpdateDocument(documentChange);
    }

    public void SaveDocument(TextDocumentIdentifier documentId) {
      if (!managersByFile.TryGetValue(documentId.Uri, out var manager)) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }

      manager.Save(documentId);
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      fileSystem.CloseDocument(documentId);
      if (managersByFile.Remove(documentId.Uri, out var manager)) {
        if (manager.CloseDocument(documentId)) {
          managersByProject.Remove(manager.Project.Uri);
        }
        await manager.CloseAsync();
        return true;
      }
      return false;
    }

    public Task<IdeState?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      if (managersByFile.TryGetValue(documentId.Uri, out var manager)) {
        return manager.GetSnapshotAfterResolutionAsync()!;
      }
      return Task.FromResult<IdeState?>(null);
    }

    public Task<CompilationAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      if (managersByFile.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.GetLastDocumentAsync()!;
      }
      return Task.FromResult<CompilationAfterParsing?>(null);
    }

    public ProjectManager? GetDocumentManager(TextDocumentIdentifier documentId) {
      return managersByFile.GetValueOrDefault(documentId.Uri);
    }

    public IEnumerable<ProjectManager> Managers => managersByProject.Values;

  }
}
