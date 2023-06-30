using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Extensions.DependencyInjection;

using System.IO;
using System.Linq;
using System.Net.Mime;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.FileSystemGlobbing;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of DocumentManagers
  /// </summary>
  public class ProjectManagerDatabase : IProjectDatabase {

    private readonly IServiceProvider services;

    private readonly Dictionary<DocumentUri, DocumentUri> projectFilesByFile = new();
    private readonly Dictionary<DocumentUri, ProjectManager> managersByProject = new();
    private readonly LanguageServerFilesystem fileSystem;
    private readonly VerificationResultCache verificationCache = new();

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

      projectFilesByFile.Add(document.Uri, profileFile.Uri);
      managersByProject[profileFile.Uri] = projectManager;
      projectManager.OpenDocument(document.Uri.ToUri());
    }

    public static DafnyProject ImplicitProject(TextDocumentIdentifier documentItem) {
      var implicitProject = new DafnyProject {
        Includes = new[] { documentItem.Uri.GetFileSystemPath() },
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
      if (!projectFilesByFile.TryGetValue(documentUri, out var projectUri)) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      var project = OpenProject(documentChange.TextDocument.Uri.ToUri());
      if (project != null) {
        var previousManager = managersByProject[projectUri];
        var _ = previousManager.CloseAsync();
        // TODO add tests that assert the affect of the new project manager, which is that nothing is migrated and last published state is lost.
        var manager = new ProjectManager(services, verificationCache, project);
        managersByProject[projectUri] = manager;
      }

      managersByProject[projectUri].UpdateDocument(documentChange);
    }

    public void SaveDocument(TextDocumentIdentifier documentId) {
      if (!projectFilesByFile.TryGetValue(documentId.Uri, out var projectUri)) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }

      managersByProject[projectUri].Save(documentId);
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      fileSystem.CloseDocument(documentId);
      if (projectFilesByFile.Remove(documentId.Uri, out var projectUri)) {
        var project = managersByProject[projectUri];
        if (await project.CloseDocument()) {
          managersByProject.Remove(project.Project.Uri);
        }
        return true;
      }
      return false;
    }

    public Task<IdeState?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      var manager = GetProjectManager(documentId);
      if (manager != null) {
        return manager.GetSnapshotAfterResolutionAsync()!;
      }

      return Task.FromResult<IdeState?>(null);
    }

    public Task<CompilationAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      var manager = GetProjectManager(documentId);
      if (manager != null) {
        return manager.GetLastDocumentAsync()!;
      }

      return Task.FromResult<CompilationAfterParsing?>(null);
    }

    public ProjectManager? GetProjectManager(TextDocumentIdentifier documentId) {
      if (projectFilesByFile.TryGetValue(documentId.Uri, out var projectFile)) {
        return managersByProject.GetValueOrDefault(projectFile);
      }

      return null;
    }

    public IEnumerable<ProjectManager> Managers => managersByProject.Values;

  }
}
