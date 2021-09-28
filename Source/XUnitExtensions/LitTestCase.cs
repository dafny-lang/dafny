using System.IO;
using System.Linq;

namespace XUnitExtensions {
  public class LitTestCase {
    public static void Run(string filePath, LitTestConfiguration config) {
      var content = File.ReadAllLines(filePath);
      var commands = content.Select(LitTestCommand.Parse).Where(c => c != null);
      foreach (var command in commands) {
        command.Run(config);
      }
    }
  }
}