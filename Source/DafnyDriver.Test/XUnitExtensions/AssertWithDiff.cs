using System.Text;
using DiffPlex;
using DiffPlex.DiffBuilder;
using DiffPlex.DiffBuilder.Model;
using Xunit.Sdk;

namespace XUnitExtensions {
  public class AssertWithDiff {
    public static void Equal(string expected, string actual) {
      if (expected != actual) {
        var diff = InlineDiffBuilder.Instance.BuildDiffModel(expected, actual);

        var message = new StringBuilder();
        message.AppendLine("AssertEqualWithDiff() Failure");
        message.AppendLine("Diff (changing expected into actual):");
        foreach (var line in diff.Lines) {
          switch (line.Type) {
            case ChangeType.Inserted:
              message.Append("+");
              break;
            case ChangeType.Deleted:
              message.Append("-");
              break;
            default:
              message.Append(" ");
              break;
          }
          message.AppendLine(line.Text);
        }
                
        throw new AssertActualExpectedException(expected, actual, message.ToString());
      }
    }
  }
}