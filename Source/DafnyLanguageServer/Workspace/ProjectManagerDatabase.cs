using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using Microsoft.Extensions.DependencyInjection;

using System.IO;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of DocumentManagers
  /// </summary>
  public class ProjectManagerDatabase : IProjectDatabase {

    private readonly IServiceProvider services;

    private readonly Dictionary<Uri, ProjectManager> managersByProject = new();
    private readonly LanguageServerFilesystem fileSystem;
    private readonly VerificationResultCache verificationCache = new();

    public ProjectManagerDatabase(IServiceProvider services) {
      this.services = services;
      this.fileSystem = services.GetRequiredService<LanguageServerFilesystem>();
    }

    public void OpenDocument(TextDocumentItem document) {
      fileSystem.OpenDocument(document);

      var projectManager = GetProjectManager(document, true, false)!;
      projectManager.OpenDocument(document.Uri.ToUri());
    }

    private DafnyProject GetProject(TextDocumentIdentifier document) {
      return FindProjectFile(document.Uri.ToUri()) ?? ImplicitProject(document);
    }

    public static DafnyProject ImplicitProject(TextDocumentIdentifier documentItem) {
      var implicitProject = new DafnyProject {
        Includes = new[] { documentItem.Uri.GetFileSystemPath() },
        Uri = documentItem.Uri.ToUri(),
        UnsavedRootFile = documentItem.Uri.ToUri()
      };
      return implicitProject;
    }

    private DafnyProject? FindProjectFile(Uri uri) {

      DafnyProject? projectFile = null;

      var folder = Path.GetDirectoryName(uri.LocalPath);
      while (!string.IsNullOrEmpty(folder)) {
        var configFileUri = new Uri(Path.Combine(folder, "dfyconfig.toml"));
        // TODO add temporal caching of configFileUri -> DafnyProject?
        if (fileSystem.Exists(configFileUri)) {
          projectFile = OpenProject(configFileUri);
          if (projectFile != null) {
            break;
          }
        }

        folder = Path.GetDirectoryName(folder);
      }

      return projectFile;
    }

    private DafnyProject? OpenProject(Uri configFileUri) {
      var errorWriter = TextWriter.Null;
      var outputWriter = TextWriter.Null;
      return DafnyProject.Open(fileSystem, configFileUri, outputWriter, errorWriter);
    }

    public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
      fileSystem.UpdateDocument(documentChange);
      var documentUri = documentChange.TextDocument.Uri;
      var manager = GetProjectManager(documentUri, false, false);
      if (manager == null) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      manager.UpdateDocument(documentChange);
    }

    public void SaveDocument(TextDocumentIdentifier documentId) {
      var manager = GetProjectManager(documentId, false, false);
      if (manager == null) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }

      manager.Save(documentId);
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      fileSystem.CloseDocument(documentId);
      var manager = GetProjectManager(documentId, false, false);
      if (manager == null) {
        return false;
      }

      if (await manager.CloseDocument()) {
        managersByProject.Remove(manager.Project.Uri);
      }
      return true;
    }

    public Task<IdeState?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      var manager = GetProjectManager(documentId, false, true);
      if (manager != null) {
        return manager.GetSnapshotAfterResolutionAsync()!;
      }

      return Task.FromResult<IdeState?>(null);
    }

    public Task<CompilationAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      var manager = GetProjectManager(documentId, false, true);
      if (manager != null) {
        return manager.GetLastDocumentAsync()!;
      }

      return Task.FromResult<CompilationAfterParsing?>(null);
    }

    public ProjectManager? GetProjectManager(TextDocumentIdentifier documentId) {
      return GetProjectManager(documentId, false, true);
    }

    // TODO add test where the project changes during a nonOpen/Change but like a code navigation
    public ProjectManager? GetProjectManager(TextDocumentIdentifier documentId, 
      bool createOnDemand, bool startIfMigrated) {
      var project = GetProject(documentId);
      var projectManager = managersByProject.GetValueOrDefault(project.Uri);

      if (projectManager != null) {
        if (!projectManager.Project.Equals(project)) {
          var _= projectManager.CloseAsync();
          projectManager.Migrate(project);
          if (startIfMigrated) {
            projectManager.StartCompilation();
          }
        }
      } else {
        if (createOnDemand) {
          projectManager = new ProjectManager(services, verificationCache, project);
        } else {
          return null;
        }
      }

      managersByProject[project.Uri] = projectManager;
      return projectManager;
    }

    public IEnumerable<ProjectManager> Managers => managersByProject.Values;
  }
}
