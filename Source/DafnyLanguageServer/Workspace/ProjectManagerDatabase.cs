using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using Microsoft.Extensions.DependencyInjection;

using System.IO;
using System.Runtime.Caching;
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
      serverOptions = services.GetRequiredService<DafnyOptions>();
      this.fileSystem = services.GetRequiredService<LanguageServerFilesystem>();
    }

    public async Task OpenDocument(TextDocumentItem document) {
      fileSystem.OpenDocument(document);

      var projectManager = await GetProjectManager(document.Uri.ToUri(), true, false)!;
      projectManager!.OpenDocument(document.Uri.ToUri());
    }


    public async Task UpdateDocument(DidChangeTextDocumentParams documentChange) {
      fileSystem.UpdateDocument(documentChange);
      var documentUri = documentChange.TextDocument.Uri;
      var manager = await GetProjectManager(documentUri.ToUri(), false, false);
      if (manager == null) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      manager.UpdateDocument(documentChange);
    }

    public async Task SaveDocument(TextDocumentIdentifier documentId) {
      var manager = await GetProjectManager(documentId.Uri.ToUri(), false, false);
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
      var manager = await GetProjectManager(documentId.Uri.ToUri(), false, true);
      if (manager != null) {
        return await manager.GetSnapshotAfterResolutionAsync()!;
      }

      return null;
    }

    public async Task<CompilationAfterParsing?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      var manager = await GetProjectManager(documentId.Uri.ToUri(), false, true);
      if (manager != null) {
        return await manager.GetLastDocumentAsync()!;
      }

      return null;
    }

    public Task<ProjectManager?> GetProjectManager(TextDocumentIdentifier documentId) {
      return GetProjectManager(documentId.Uri.ToUri(), false, true);
    }

    public async Task<ProjectManager?> GetProjectManager(Uri uri,
      bool createOnDemand, bool startIfMigrated) {
      var project = GetProject(uri);
      var projectManagerForFile = managersBySourceFile.GetValueOrDefault(uri);

      if (projectManagerForFile != null) {
        var filesProjectHasChanged = !projectManagerForFile.Project.Equals(project);
        if (filesProjectHasChanged) {
          var projectFileHasChanged = projectManagerForFile.Project.Uri == project.Uri;
          if (projectFileHasChanged) {
            await projectManagerForFile.CloseAsync();
          } else {
            await projectManagerForFile.CloseDocument();
          }
          projectManagerForFile = new ProjectManager(services, verificationCache, project);
          projectManagerForFile.OpenDocument(uri);
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

      managersBySourceFile[uri] = projectManagerForFile;
      managersByProject[project.Uri] = projectManagerForFile;
      return projectManagerForFile;
    }

    public DafnyProject GetProject(Uri sourceFile) {
      return FindProjectFile(sourceFile) ?? ImplicitProject(sourceFile);
    }

    public static DafnyProject ImplicitProject(Uri uri) {
      var implicitProject = new DafnyProject {
        Includes = new[] { uri.LocalPath },
        Uri = uri,
        IsImplicitProject = true
      };
      return implicitProject;
    }

    private DafnyProject? FindProjectFile(Uri sourceUri) {
      DafnyProject? projectFile = null;

      var folder = Path.GetDirectoryName(sourceUri.LocalPath);
      while (!string.IsNullOrEmpty(folder) && projectFile == null) {
        projectFile = OpenProjectFromFolder(folder);

        if (projectFile != null && projectFile.Uri != sourceUri && projectFile.ContainsSourceFile(sourceUri) == false) {
          projectFile = null;
        }

        folder = Path.GetDirectoryName(folder);
      }

      if (projectFile != null && projectFile.Uri != sourceUri && !serverOptions.Get(ServerCommand.ProjectMode)) {
        projectFile.Uri = sourceUri;
        projectFile.IsImplicitProject = true;
        projectFile.Includes = new[] { sourceUri.LocalPath };
      }

      return projectFile;
    }

    public const int ProjectFileCacheExpiryTime = 100;
    private readonly MemoryCache projectFilePerFolderCache = new("projectFiles");
    private readonly object nullRepresentative = new(); // Needed because you can't store null in the MemoryCache, but that's a value we want to cache.
    private readonly DafnyOptions serverOptions;

    private DafnyProject? OpenProjectFromFolder(string folderPath) {
      var cachedResult = projectFilePerFolderCache.Get(folderPath);
      if (cachedResult != null) {
        return cachedResult == nullRepresentative ? null : (DafnyProject?)cachedResult;
      }

      var result = OpenProjectFromFolderUncached(folderPath);
      projectFilePerFolderCache.Set(new CacheItem(folderPath, (object?)result ?? nullRepresentative), new CacheItemPolicy {
        AbsoluteExpiration = new DateTimeOffset(DateTime.Now.Add(TimeSpan.FromMilliseconds(ProjectFileCacheExpiryTime)))
      });
      return result?.Clone();
    }

    private DafnyProject? OpenProjectFromFolderUncached(string folderPath) {
      var configFileUri = new Uri(Path.Combine(folderPath, DafnyProject.FileName));
      DafnyProject? result = null;
      if (fileSystem.Exists(configFileUri)) {
        result = DafnyProject.Open(fileSystem, configFileUri, TextWriter.Null, TextWriter.Null);
      }

      if (result != null) {
        return result;
      }

      var parent = Path.GetDirectoryName(folderPath);
      return parent == null ? null : OpenProjectFromFolder(parent);
    }

    public IEnumerable<ProjectManager> Managers => managersByProject.Values;
  }
}
