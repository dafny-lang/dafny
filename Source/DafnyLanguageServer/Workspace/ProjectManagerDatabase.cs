using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.Caching;
using System.Threading.Tasks;
using DafnyCore;
using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Contains a collection of ProjectManagers
  /// </summary>
  public class ProjectManagerDatabase : IProjectDatabase {

    private readonly object myLock = new();

    private readonly CreateProjectManager createProjectManager;
    private readonly ILogger<ProjectManagerDatabase> logger;

    private readonly Dictionary<Uri, ProjectManager> managersByProject = new();
    private readonly Dictionary<Uri, ProjectManager> managersBySourceFile = new();
    private readonly LanguageServerFilesystem fileSystem;
    private readonly VerificationResultCache verificationCache = new();
    private readonly TaskScheduler scheduler;
    private readonly DafnyOptions serverOptions;
    private CachingProjectFileOpener projectFileOpener;

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
      projectFileOpener = new CachingProjectFileOpener(fileSystem, serverOptions, Token.Ide);
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
      logger.LogDebug($"project manager found for {documentId.Uri}");
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

        bool triggerCompilation = false;
        if (projectManagerForFile != null) {

          var filesProjectHasChanged = !projectManagerForFile.Project.Equals(project);
          if (filesProjectHasChanged) {
            logger.LogDebug($"Migrating file {uri} from project {projectManagerForFile.Project.Uri} to project {project.Uri}");

            var projectFileContentHasChanged = projectManagerForFile.Project.Uri == project.Uri;
            if (projectFileContentHasChanged) {
              managersByProject.Remove(project.Uri);
            }
            var previousProjectHasNoDocuments = projectManagerForFile.CloseDocument(projectManagerForFile.Project.Uri);
            if (previousProjectHasNoDocuments) {
              // Enable garbage collection
              managersByProject.Remove(projectManagerForFile.Project.Uri);
            }

            projectManagerForFile = managersByProject.GetValueOrDefault(project.Uri) ??
                                    createProjectManager(scheduler, verificationCache, project);
            projectManagerForFile.OpenDocument(uri, true);
            triggerCompilation = true;
          }
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
      return await projectFileOpener.TryFindProject(uri) ?? ImplicitProject(uri);
    }

    public static DafnyProject ImplicitProject(Uri uri) {
      var implicitProject = new DafnyProject(
        null,
        uri, null,
        new[] { uri.LocalPath }.ToHashSet(),
        new HashSet<string>(),
        new Dictionary<string, object>());
      return implicitProject;
    }

    public IEnumerable<ProjectManager> Managers => managersByProject.Values;
    public void Dispose() {
      foreach (var manager in Managers) {
        manager.Dispose();
      }
    }
  }
}