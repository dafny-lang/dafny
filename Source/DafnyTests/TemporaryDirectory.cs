using System;
using System.IO;

namespace DafnyTests {
  public class TemporaryDirectory : IDisposable {
    public readonly DirectoryInfo DirInfo;

    public TemporaryDirectory(string parent, string prefix = "") {
      string dirPath;
      // Loop until we pick a random name that isn't already taken.
      do {
        dirPath = Path.Combine(parent, prefix + Path.GetRandomFileName());
      } while (File.Exists(dirPath) || Directory.Exists(dirPath));

      DirInfo = Directory.CreateDirectory(dirPath);
    }

    public void Dispose() {
      Dispose(true);
    }

    ~TemporaryDirectory() {
      Dispose(false);
    }
        
    protected virtual void Dispose(bool disposing) {
      SafeDelete();
    }
        
    public void SafeDelete() {
      try {
        DirInfo.Delete(true);
      } catch {
        // Best effort only
      }
    }
  }
}