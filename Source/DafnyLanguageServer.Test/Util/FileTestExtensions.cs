using System;
using System.IO;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class FileTestExtensions {

  public static async Task WriteWhenUnlocked(string fullPath, string text) {
    await using var fs = await WaitForFileToUnlock(fullPath, FileMode.Create,
      FileAccess.Write, FileShare.Read);
    await using var sw = new StreamWriter(fs);
    await sw.WriteAsync(text);
  }

  public static async Task<FileStream> WaitForFileToUnlock(string fullPath, FileMode mode, FileAccess access, FileShare share) {
    for (int numTries = 0; numTries < 100; numTries++) {
      FileStream fs = null;
      try {
        fs = new FileStream(fullPath, mode, access, share);
        return fs;
      } catch (IOException) {
        if (fs != null) {
          await fs.DisposeAsync();
        }
        await Task.Delay(50);
      }
    }

    throw new Exception("File did not unlock in time");
  }
}