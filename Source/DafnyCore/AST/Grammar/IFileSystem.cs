using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyCore.Options;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;

namespace Microsoft.Dafny;

public record FileSnapshot(TextReader Reader, int? Version);

public interface IFileSystem {
  FileSnapshot ReadFile(Uri uri);

  public bool Exists(Uri path);
  DirectoryInfoBase GetDirectoryInfoBase(string root);
}

public class InMemoryFileSystem : IFileSystem {
  private readonly IReadOnlyDictionary<Uri, string> files;

  public InMemoryFileSystem(IReadOnlyDictionary<Uri, string> files) {
    this.files = files;
  }

  public FileSnapshot ReadFile(Uri uri) {
    if (files.TryGetValue(uri, out var entry)) {
      return new FileSnapshot(new StringReader(entry), null);
    }

    return OnDiskFileSystem.Instance.ReadFile(uri);
  }

  public bool Exists(Uri path) {
    return files.ContainsKey(path) || OnDiskFileSystem.Instance.Exists(path);
  }

  public DirectoryInfoBase GetDirectoryInfoBase(string root) {
    var inMemoryFiles = files.Keys.Select(openFileUri => openFileUri.LocalPath);
    var inMemory = new InMemoryDirectoryInfoFromDotNet8(root, inMemoryFiles);
    return new CombinedDirectoryInfo([inMemory, OnDiskFileSystem.Instance.GetDirectoryInfoBase(root)]);
  }
}

public class OnDiskFileSystem : IFileSystem {
  public static readonly IFileSystem Instance = new OnDiskFileSystem();

  private OnDiskFileSystem() {
  }

  public FileSnapshot ReadFile(Uri uri) {
    return new FileSnapshot(new StreamReader(uri.LocalPath), null);
  }

  public bool Exists(Uri path) {
    return File.Exists(path.LocalPath);
  }

  public DirectoryInfoBase GetDirectoryInfoBase(string root) {
    return new CustomDirectoryInfoWrapper(new DirectoryInfo(root!));
  }
}