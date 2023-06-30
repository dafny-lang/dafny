using System;
using System.IO;

namespace Microsoft.Dafny;

public interface IFileSystem {
  TextReader ReadFile(Uri uri);
}

public class OnDiskFileSystem : IFileSystem {
  public static readonly IFileSystem Instance = new OnDiskFileSystem();
  public TextReader ReadFile(Uri uri) {
    return new StreamReader(uri.LocalPath);
  }
}