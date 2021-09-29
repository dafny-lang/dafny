using System.IO;
using System.Linq;
using Xunit;

namespace XUnitExtensions {
  public class LitTestCase {
    public static void Run(string filePath, LitTestConfiguration config) {
      // TODO: Deal with %s, and %t
      // TODO: apply this for MainMethod versions of %dafny etc.:
      // Lit always uses the parent directory of a test file as the current directory,
      // so other file paths have to be interpreted to be relative to the output directory instead.
      // otherFiles.Add(Path.Join(Path.GetDirectoryName(filePath), value));
      var content = File.ReadAllLines(filePath);
      var commands = content.Select(line => ILitCommand.Parse(line, config))
                            .Where(c => c != null);
      foreach (var command in commands) {
        var (exitCode, output) = command.Execute();
        Assert.True(exitCode != 0, $"Command failed with output:\n{output}");
      }
    }
  }
}