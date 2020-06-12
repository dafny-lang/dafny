using System;
using System.IO;

namespace DafnyTests {
    public class TemporaryDirectory : IDisposable {
        public readonly DirectoryInfo Dir;

        public TemporaryDirectory() {
            string dirPath;
            do {
                dirPath = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
            } while (File.Exists(dirPath) || Directory.Exists(dirPath));

            Dir = Directory.CreateDirectory(dirPath);
        }

        public void Dispose() {
            // TODO-RS: Be way more careful with finalizers/threading/etc.
            Dir.Delete(true);
        }
    }
}