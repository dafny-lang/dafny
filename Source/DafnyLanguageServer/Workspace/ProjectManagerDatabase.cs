using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Runtime.Caching;
using System.Threading.Tasks;
using DafnyCore;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of ProjectManagers
  /// </summary>
  public class ProjectManagerDatabase : IProjectDatabase {
    public static readonly Option<int> ProjectFileCacheExpiry = new("--project-file-cache-expiry", () => DefaultProjectFileCacheExpiryTime,
      @"How many milliseconds the server will cache project file contents".TrimStart()) {
      IsHidden = true
    };

    static ProjectManagerDatabase() {
      DooFile.RegisterNoChecksNeeded(ProjectFileCacheExpiry, false);
    }

    private readonly object myLock = new();
    public const int DefaultProjectFileCacheExpiryTime = 100;

    private readonly CreateProjectManager createProjectManager;
    private readonly ILogger<ProjectManagerDatabase> logger;

    private readonly Dictionary<Uri, ProjectManager> managersByProject = new();
    private readonly Dictionary<Uri, ProjectManager> managersBySourceFile = new();
    private readonly LanguageServerFilesystem fileSystem;
    private readonly VerificationResultCache verificationCache = new();
    private readonly CustomStackSizePoolTaskScheduler scheduler;
    private readonly MemoryCache projectFilePerFolderCache = new("projectFiles");
    private readonly object nullRepresentative = new(); // Needed because you can't store null in the MemoryCache, but that's a value we want to cache.
    private readonly DafnyOptions serverOptions;

    private const int stackSize = 10 * 1024 * 1024;

    public ProjectManagerDatabase(
      LanguageServerFilesystem fileSystem,
      DafnyOptions serverOptions,
      CreateProjectManager createProjectManager,
      ILogger<ProjectManagerDatabase> logger) {
      this.createProjectManager = createProjectManager;
      this.logger = logger;
      this.fileSystem = fileSystem;
      this.serverOptions = serverOptions;
      this.scheduler = CustomStackSizePoolTaskScheduler.Create(stackSize, serverOptions.VcsCores);
    }

    public async Task OpenDocument(TextDocumentItem document) {
      // When we have caching of all compilation components, we might not need to do this change detection at the start
      var changed = fileSystem.OpenDocument(document);
      await GetProjectManager(document, true, changed);
    }

    public async Task UpdateDocument(DidChangeTextDocumentParams documentChange) {
      var success = fileSystem.UpdateDocument(documentChange);
      if (!success) {
        throw new ArgumentException("the document change ranges did not match ranges inside the documents");
      }
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

    public void CloseDocument(TextDocumentIdentifier documentId) {
      fileSystem.CloseDocument(documentId);

      lock (myLock) {
        if (!managersBySourceFile.Remove(documentId.Uri.ToUri(), out var manager)) {
          return;
        }

        if (manager.CloseDocument(documentId.Uri.ToUri())) {
          managersByProject.Remove(manager.Project.Uri, out _);
        }
      }
    }

    public async Task<IdeState?> GetParsedDocumentNormalizeUri(TextDocumentIdentifier documentId) {
      // Resolves drive letter capitalisation issues in Windows that occur when this method is called
      // from an in-process client without serializing documentId
      var normalizedUri = DocumentUri.From(documentId.Uri.ToString());
      documentId = documentId with {
        Uri = normalizedUri
      };
      var manager = await GetProjectManager(documentId, false);
      if (manager != null) {
        return await manager.GetStateAfterParsingAsync();
      }

      return null;
    }

    public Task<IdeState?> GetResolvedDocumentAsyncNormalizeUri(TextDocumentIdentifier documentId) {
      // Resolves drive letter capitalisation issues in Windows that occur when this method is called
      // from an in-process client without serializing documentId
      var normalizedUri = DocumentUri.From(documentId.Uri.ToString());
      documentId = documentId with {
        Uri = normalizedUri
      };
      return GetResolvedDocumentAsyncInternal(documentId);
    }

    public async Task<IdeState?> GetResolvedDocumentAsyncInternal(TextDocumentIdentifier documentId) {
      var manager = await GetProjectManager(documentId, false);
      if (manager != null) {
        return await manager.GetStateAfterResolutionAsync();
      }

      return null;
    }

    public Task<ProjectManager?> GetProjectManager(TextDocumentIdentifier documentId) {
      return GetProjectManager(documentId, false);
    }

    private async Task<ProjectManager?> GetProjectManager(TextDocumentIdentifier documentId, bool createOnDemand, bool changedOnOpen = false) {
      var uri = documentId.Uri.ToUri();
      if (!fileSystem.Exists(uri)) {
        return null;
      }

      var project = await GetProject(uri);

      lock (myLock) {
        var projectManagerForFile = managersBySourceFile.GetValueOrDefault(uri);

        if (projectManagerForFile is { IsDisposed: true }) {
          // Defensive coding
          logger.LogError("Found disposed project manager through managersBySourceFile.");
          projectManagerForFile = null;
        }

        bool triggerCompilation;
        if (projectManagerForFile != null) {

          var filesProjectHasChanged = !projectManagerForFile.Project.Equals(project);
          if (filesProjectHasChanged) {
            logger.LogDebug($"Migrating file {uri} from project {projectManagerForFile.Project.Uri} to project {project.Uri}");
            var previousProjectHasNoDocuments = projectManagerForFile.CloseDocument(projectManagerForFile.Project.Uri);
            if (previousProjectHasNoDocuments) {
              // Enable garbage collection
              managersByProject.Remove(projectManagerForFile.Project.Uri);
            }

            projectManagerForFile = managersByProject.GetValueOrDefault(project.Uri) ??
                                    createProjectManager(scheduler, verificationCache, project);
            projectManagerForFile.OpenDocument(uri, true);
          }

          triggerCompilation = true;
        } else {
          var managerForProject = managersByProject.GetValueOrDefault(project.Uri);
          if (managerForProject is { IsDisposed: true }) {
            // Defensive coding
            logger.LogError("Found disposed project manager through managersByProject.");
            managerForProject = null;
          }

          if (managerForProject != null) {
            projectManagerForFile = managerForProject;
            triggerCompilation = changedOnOpen;
          } else {
            if (createOnDemand) {
              projectManagerForFile = createProjectManager(scheduler, verificationCache, project);
              triggerCompilation = true;
            } else {
              return null;
            }
          }
        }

        managersBySourceFile[uri] = projectManagerForFile;
        managersByProject[project.Uri] = projectManagerForFile;
        projectManagerForFile.OpenDocument(uri, triggerCompilation);
        return projectManagerForFile;
      }
    }

    public async Task<DafnyProject> GetProject(Uri uri) {
      return uri.LocalPath.EndsWith(DafnyProject.FileName)
        ? await DafnyProject.Open(fileSystem, serverOptions, uri, Token.Ide)
        : (await FindProjectFile(uri) ?? ImplicitProject(uri));
    }

    public static DafnyProject ImplicitProject(Uri uri) {
      var implicitProject = new DafnyProject(
        uri, null,
        new[] { uri.LocalPath }.ToHashSet(),
        new HashSet<string>(),
        new Dictionary<string, object>());
      return implicitProject;
    }

    private async Task<DafnyProject?> FindProjectFile(Uri sourceUri) {
      DafnyProject? projectFile = null;

      var folder = Path.GetDirectoryName(sourceUri.LocalPath);
      while (!string.IsNullOrEmpty(folder) && projectFile == null) {
        projectFile = await OpenProjectInFolder(folder);

        if (projectFile != null && projectFile.Uri != sourceUri &&
            !(projectFile.Errors.HasErrors || projectFile.ContainsSourceFile(sourceUri))) {
          projectFile = null;
        }

        folder = Path.GetDirectoryName(folder);
      }

      return projectFile;
    }

    private async Task<DafnyProject?> OpenProjectInFolder(string folderPath) {
      var cacheExpiry = serverOptions.Get(ProjectFileCacheExpiry);
      if (cacheExpiry == 0) {
        return await OpenProjectInFolderUncached(folderPath);
      }

      var cachedResult = projectFilePerFolderCache.Get(folderPath);
      if (cachedResult != null) {
        return cachedResult == nullRepresentative ? null : ((DafnyProject?)cachedResult)?.Clone();
      }

      var result = await OpenProjectInFolderUncached(folderPath);
      projectFilePerFolderCache.Set(new CacheItem(folderPath, (object?)result ?? nullRepresentative), new CacheItemPolicy {
        AbsoluteExpiration = new DateTimeOffset(DateTime.Now.Add(TimeSpan.FromMilliseconds(cacheExpiry)))
      });
      return result?.Clone();
    }

    private Task<DafnyProject?> OpenProjectInFolderUncached(string folderPath) {
      var configFileUri = new Uri(Path.Combine(folderPath, DafnyProject.FileName));
      if (!fileSystem.Exists(configFileUri)) {
        return Task.FromResult<DafnyProject?>(null);
      }

      return DafnyProject.Open(fileSystem, serverOptions, configFileUri, Token.Ide)!;
    }

    public IEnumerable<ProjectManager> Managers => managersByProject.Values;
    public void Dispose() {
      foreach (var manager in Managers) {
        manager.Dispose();
      }
    }
  }
}
