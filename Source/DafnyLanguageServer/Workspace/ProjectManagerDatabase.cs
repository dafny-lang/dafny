using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Runtime.Caching;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of ProjectManagers
  /// </summary>
  public class ProjectManagerDatabase : IProjectDatabase, IDisposable {
    private object myLock = new();
    public const int ProjectFileCacheExpiryTime = 100;

    private readonly CreateProjectManager createProjectManager;
    private readonly ILogger<ProjectManagerDatabase> logger;
    private readonly ExecutionEngine boogieEngine;

    private readonly Dictionary<Uri, ProjectManager> managersByProject = new();
    private readonly Dictionary<Uri, ProjectManager> managersBySourceFile = new();
    private readonly LanguageServerFilesystem fileSystem;
    private readonly VerificationResultCache verificationCache = new();
    private readonly MemoryCache projectFilePerFolderCache = new("projectFiles");
    private readonly object nullRepresentative = new(); // Needed because you can't store null in the MemoryCache, but that's a value we want to cache.
    private readonly DafnyOptions serverOptions;

    public ProjectManagerDatabase(
      LanguageServerFilesystem fileSystem,
      DafnyOptions serverOptions,
      CreateProjectManager createProjectManager,
      ILogger<ProjectManagerDatabase> logger) {
      this.createProjectManager = createProjectManager;
      this.logger = logger;
      this.fileSystem = fileSystem;
      this.serverOptions = serverOptions;
      boogieEngine = new ExecutionEngine(serverOptions, verificationCache);
    }

    public async Task OpenDocument(TextDocumentItem document) {
      fileSystem.OpenDocument(document);
      var projectManager = await GetProjectManager(document, true)!;
      projectManager!.OpenDocument(document.Uri.ToUri());
    }


    public async Task UpdateDocument(DidChangeTextDocumentParams documentChange) {
      fileSystem.UpdateDocument(documentChange);
      var documentUri = documentChange.TextDocument.Uri;
      var manager = await GetProjectManager(documentUri, false);
      if (manager == null) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      manager.UpdateDocument(documentChange);
    }

    public async Task SaveDocument(TextDocumentIdentifier documentId) {
      var manager = await GetProjectManager(documentId, false);
      if (manager == null) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }

      manager.Save(documentId);
    }

    public async Task CloseDocumentAsync(TextDocumentIdentifier documentId) {
      fileSystem.CloseDocument(documentId);

      Task close;
      lock (myLock) {
        if (!managersBySourceFile.Remove(documentId.Uri.ToUri(), out var manager)) {
          return;
        }

        if (manager.CloseDocument(out close)) {
          managersByProject.Remove(manager.Project.Uri, out _);
        }
      }
      await close;
    }

    public async Task<IdeState?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      var manager = await GetProjectManager(documentId, false);
      if (manager != null) {
        return await manager.GetSnapshotAfterResolutionAsync()!;
      }

      return null;
    }

    public async Task<CompilationAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      // Resolves drive letter capitalisation issues in Windows that occur when this method is called
      // from an in-process client without serializing documentId
      var normalizedUri = DocumentUri.From(documentId.Uri.ToString());
      documentId = documentId with {
        Uri = normalizedUri
      };
      var manager = await GetProjectManager(documentId, false);
      if (manager != null) {
        return await manager.GetLastDocumentAsync()!;
      }

      return null;
    }

    public Task<ProjectManager?> GetProjectManager(TextDocumentIdentifier documentId) {
      return GetProjectManager(documentId, false);
    }

    private async Task<ProjectManager?> GetProjectManager(TextDocumentIdentifier documentId, bool createOnDemand) {
      if (!fileSystem.Exists(documentId.Uri.ToUri())) {
        return null;
      }

      var project = await GetProject(documentId);

      lock (myLock) {
        var projectManagerForFile = managersBySourceFile.GetValueOrDefault(documentId.Uri.ToUri());

        if (projectManagerForFile != null) {
          var filesProjectHasChanged = !projectManagerForFile.Project.Equals(project);
          if (filesProjectHasChanged) {
            var projectFileHasChanged = projectManagerForFile.Project.Uri == project.Uri;
            if (projectFileHasChanged) {
              var _ = projectManagerForFile.CloseAsync();
            } else {
              projectManagerForFile.CloseDocument(out _);
            }

            projectManagerForFile = createProjectManager(boogieEngine, project);
            projectManagerForFile.OpenDocument(documentId.Uri.ToUri());
          }
        } else {
          var managerForProject = managersByProject.GetValueOrDefault(project.Uri);
          if (managerForProject != null) {
            projectManagerForFile = managerForProject;
          } else {
            if (createOnDemand) {
              projectManagerForFile = createProjectManager(boogieEngine, project);
            } else {
              return null;
            }
          }
        }

        managersBySourceFile[documentId.Uri.ToUri()] = projectManagerForFile;
        managersByProject[project.Uri] = projectManagerForFile;
        return projectManagerForFile;
      }
    }

    private async Task<DafnyProject> GetProject(TextDocumentIdentifier document) {
      return (await FindProjectFile(document.Uri.ToUri())) ?? ImplicitProject(document);
    }

    public static DafnyProject ImplicitProject(TextDocumentIdentifier documentItem) {
      var implicitProject = new DafnyProject {
        Includes = new[] { documentItem.Uri.GetFileSystemPath() },
        Uri = documentItem.Uri.ToUri(),
        IsImplicitProject = true
      };
      return implicitProject;
    }

    private async Task<DafnyProject?> FindProjectFile(Uri sourceUri) {
      DafnyProject? projectFile = null;

      var folder = Path.GetDirectoryName(sourceUri.LocalPath);
      while (!string.IsNullOrEmpty(folder) && projectFile == null) {
        projectFile = await OpenProjectInFolder(folder);

        if (projectFile != null && projectFile.Uri != sourceUri && projectFile.ContainsSourceFile(sourceUri) == false) {
          projectFile = null;
        }

        folder = Path.GetDirectoryName(folder);
      }

      if (projectFile != null && !serverOptions.Get(ServerCommand.ProjectMode)) {
        projectFile.Uri = sourceUri;
        projectFile.IsImplicitProject = true;
        projectFile.Includes = new[] { sourceUri.LocalPath };
      }

      return projectFile;
    }

    private async Task<DafnyProject?> OpenProjectInFolder(string folderPath) {
      var cachedResult = projectFilePerFolderCache.Get(folderPath);
      if (cachedResult != null) {
        return cachedResult == nullRepresentative ? null : (DafnyProject?)cachedResult;
      }

      var result = await OpenProjectInFolderUncached(folderPath);
      projectFilePerFolderCache.Set(new CacheItem(folderPath, (object?)result ?? nullRepresentative), new CacheItemPolicy {
        AbsoluteExpiration = new DateTimeOffset(DateTime.Now.Add(TimeSpan.FromMilliseconds(ProjectFileCacheExpiryTime)))
      });
      return result?.Clone();
    }

    private Task<DafnyProject?> OpenProjectInFolderUncached(string folderPath) {
      var configFileUri = new Uri(Path.Combine(folderPath, DafnyProject.FileName));
      if (!fileSystem.Exists(configFileUri)) {
        return Task.FromResult<DafnyProject?>(null);
      }

      return DafnyProject.Open(fileSystem, configFileUri, TextWriter.Null, TextWriter.Null);
    }

    public IEnumerable<ProjectManager> Managers => managersByProject.Values;
    public void Dispose() {
      boogieEngine.Dispose();
      foreach (var manager in Managers) {
        manager.Dispose();
      }
    }
  }
}
