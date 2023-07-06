using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class CombinedDirectoryInfo : DirectoryInfoBase {
  public DirectoryInfoBase[] Parts { get; }

  public CombinedDirectoryInfo(DirectoryInfoBase[] parts) {
    this.Parts = parts;
  }

  public override string Name => Parts[0].Name;
  public override string FullName => Parts[0].FullName;

  public override DirectoryInfoBase ParentDirectory =>
    new CombinedDirectoryInfo(Parts.Select(part => part.ParentDirectory).ToArray());

  public override IEnumerable<FileSystemInfoBase> EnumerateFileSystemInfos() {
    var results = Parts.SelectMany(part => part.EnumerateFileSystemInfos()).ToArray();
    var directories = results.OfType<DirectoryInfoBase>().GroupBy(d => d.FullName).Select(directoryGroup => {
      var directoryParts = directoryGroup.ToArray();
      return directoryParts.Length > 1 ? new CombinedDirectoryInfo(directoryParts) : directoryParts[0];
    });

    return results.OfType<FileInfoBase>().DistinctBy(f => f.FullName).Concat<FileSystemInfoBase>(directories);
  }

  public override DirectoryInfoBase GetDirectory(string path) {
    return new CombinedDirectoryInfo(Parts.Select(part => part.GetDirectory(path)).ToArray());
  }

  public override FileInfoBase GetFile(string path) {
    Exception? lastException = null;
    foreach (var part in Parts) {
      try {
        return part.GetFile(path);
      } catch (IOException e) {
        lastException = e;
      }
    }

    throw lastException!;
  }
}