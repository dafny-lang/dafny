#nullable enable
using System;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny;

public class ProjectFileOpener {
  private readonly IFileSystem fileSystem;
  private readonly IOrigin origin;

  public ProjectFileOpener(IFileSystem fileSystem, IOrigin origin) {
    this.fileSystem = fileSystem;
    this.origin = origin;
  }

  public async Task<DafnyProject?> TryFindProject(Uri uri) {
    return uri.LocalPath.EndsWith(DafnyProject.FileName)
      ? await DafnyProject.Open(fileSystem, uri, origin)
      : await FindProjectFile(uri);
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

  protected virtual Task<DafnyProject?> OpenProjectInFolder(string folderPath) {
    Uri configFileUri;
    try {
      configFileUri = new Uri(Path.Combine(folderPath, DafnyProject.FileName));
    } catch (Exception) {
      // On Windows systems, the URI "/Untitled-1" is not recognized for example
      return Task.FromResult<DafnyProject?>(null);
    }

    if (!fileSystem.Exists(configFileUri)) {
      return Task.FromResult<DafnyProject?>(null);
    }

    return DafnyProject.Open(fileSystem, configFileUri, origin)!;
  }
}