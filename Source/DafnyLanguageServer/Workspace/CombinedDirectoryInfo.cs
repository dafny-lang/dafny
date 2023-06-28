using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class CombinedDirectoryInfo : DirectoryInfoBase {
  private readonly DirectoryInfoBase[] parts;

  public CombinedDirectoryInfo(DirectoryInfoBase[] parts) {
    this.parts = parts;
  }

  public override string Name => parts[0].Name;
  public override string FullName => parts[0].FullName;

  public override DirectoryInfoBase ParentDirectory =>
    new CombinedDirectoryInfo(parts.Select(part => part.ParentDirectory).ToArray());

  public override IEnumerable<FileSystemInfoBase> EnumerateFileSystemInfos() {
    return parts.SelectMany(part => part.EnumerateFileSystemInfos());
  }

  public override DirectoryInfoBase GetDirectory(string path) {
    return new CombinedDirectoryInfo(parts.Select(part => part.GetDirectory(path)).ToArray());
  }

  public override FileInfoBase GetFile(string path) {
    Exception? lastException = null;
    foreach (var part in parts) {
      try {
        return part.GetFile(path);
      } catch (IOException e) {
        lastException = e;
      }
    }

    throw lastException!;
  }
}