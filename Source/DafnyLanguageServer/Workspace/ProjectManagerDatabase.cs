using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using Microsoft.Extensions.DependencyInjection;

using System.IO;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of ProjectManagers
  /// </summary>
  public class ProjectManagerDatabase : IProjectDatabase {

    private readonly IServiceProvider services;

    private readonly Dictionary<Uri, ProjectManager> managersByProject = new();
    private readonly Dictionary<Uri, ProjectManager> managersBySourceFile = new();
    private readonly LanguageServerFilesystem fileSystem;
    private readonly VerificationResultCache verificationCache = new();

    public ProjectManagerDatabase(IServiceProvider services) {
      this.services = services;
      this.fileSystem = services.GetRequiredService<LanguageServerFilesystem>();
    }

    public async Task OpenDocument(TextDocumentItem document) {
      fileSystem.OpenDocument(document);

      var projectManager = await GetProjectManager(document, true, false)!;
      projectManager!.OpenDocument(document.Uri.ToUri());
    }

    private DafnyProject GetProject(TextDocumentIdentifier document) {
      return FindProjectFile(document.Uri.ToUri()) ?? ImplicitProject(document);
    }

    public static DafnyProject ImplicitProject(TextDocumentIdentifier documentItem) {
      var implicitProject = new DafnyProject {
        Includes = new [] { documentItem.Uri.GetFileSystemPath() },
        Uri = documentItem.Uri.ToUri(),
        IsImplicitProject = true
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

    public async Task UpdateDocument(DidChangeTextDocumentParams documentChange) {
      fileSystem.UpdateDocument(documentChange);
      var documentUri = documentChange.TextDocument.Uri;
      var manager = await GetProjectManager(documentUri, false, false);
      if (manager == null) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      manager.UpdateDocument(documentChange);
    }

    public async Task SaveDocument(TextDocumentIdentifier documentId) {
      var manager = await GetProjectManager(documentId, false, false);
      if (manager == null) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }

      manager.Save(documentId);
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      fileSystem.CloseDocument(documentId);

      managersBySourceFile.TryGetValue(documentId.Uri.ToUri(), out var manager);
      if (manager == null) {
        return false;
      }

      if (await manager.CloseDocument()) {
        managersByProject.Remove(manager.Project.Uri);
      }

      return true;
    }

    public async Task<IdeState?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      var manager = await GetProjectManager(documentId, false, true);
      if (manager != null) {
        return await manager.GetSnapshotAfterResolutionAsync()!;
      }

      return null;
    }

    public async Task<CompilationAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      var manager = await GetProjectManager(documentId, false, true);
      if (manager != null) {
        return await manager.GetLastDocumentAsync()!;
      }

      return null;
    }

    public Task<ProjectManager?> GetProjectManager(TextDocumentIdentifier documentId) {
      return GetProjectManager(documentId, false, true);
    }

    public async Task<ProjectManager?> GetProjectManager(TextDocumentIdentifier documentId, 
      bool createOnDemand, bool startIfMigrated) {
      var project = GetProject(documentId);
      var projectManagerForFile = managersBySourceFile.GetValueOrDefault(documentId.Uri.ToUri());

      if (projectManagerForFile != null) {
        if (!projectManagerForFile.Project.Equals(project)) {
          await projectManagerForFile.CloseDocument();
          projectManagerForFile = new ProjectManager(services, verificationCache, project);
          // TODO does this OpenDocument call trigger too much verification?
          // TODO do we have issues with previous ideState not being properly accounted for? Should we always publish reset notifications when a new project is created?
          projectManagerForFile.OpenDocument(documentId.Uri.ToUri());
        }
      } else {
        var managerForProject = managersByProject.GetValueOrDefault(project.Uri);
        if (managerForProject != null) {
          projectManagerForFile = managerForProject;
        } else {
          if (createOnDemand) {
            projectManagerForFile = new ProjectManager(services, verificationCache, project);
          } else {
            return null;
          }
        }
      }

      managersBySourceFile[documentId.Uri.ToUri()] = projectManagerForFile;
      managersByProject[project.Uri] = projectManagerForFile;
      return projectManagerForFile;
    }

    public IEnumerable<ProjectManager> Managers => managersByProject.Values;
  }
}
