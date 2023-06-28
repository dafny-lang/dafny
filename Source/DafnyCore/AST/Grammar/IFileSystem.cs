using System;
using System.IO;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;

namespace Microsoft.Dafny;

public interface IFileSystem {
  TextReader ReadFile(Uri uri);

  public bool Exists(Uri path);
  DirectoryInfoBase GetDirectoryInfoBase(Uri uri);
}

public class OnDiskFileSystem : IFileSystem {
  public static readonly IFileSystem Instance = new OnDiskFileSystem();

  private OnDiskFileSystem() {
  }

  public TextReader ReadFile(Uri uri) {
    return new StreamReader(uri.LocalPath);
  }

  public bool Exists(Uri path) {
    return File.Exists(path.LocalPath);
  }

  public DirectoryInfoBase GetDirectoryInfoBase(Uri uri) {
    var root = Path.GetDirectoryName(uri.LocalPath);
    return new DirectoryInfoWrapper(new DirectoryInfo(root!));
  }
}