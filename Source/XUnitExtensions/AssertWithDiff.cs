using System.Text;
using DiffPlex;
using DiffPlex.DiffBuilder;
using DiffPlex.DiffBuilder.Model;
using Xunit.Sdk;

namespace XUnitExtensions {
  public class AssertWithDiff {

    public static string? GetDiffMessage(string expected, string actual) {
      var diff = InlineDiffBuilder.Instance.BuildDiffModel(expected, actual, false);
      if (!diff.HasDifferences) {
        return null;
      }

      var message = new StringBuilder();
      message.AppendLine("AssertEqualWithDiff() Failure");
      message.AppendLine("Diff (changing expected into actual):");
      foreach (var line in diff.Lines) {
        var prefix = line.Type switch {
          ChangeType.Inserted => '+',
          ChangeType.Deleted => '-',
          _ => ' '
        };
        message.Append(prefix);
        message.AppendLine(line.Text);
      }

      return message.ToString();
    }

    public static void Equal(string expected, string actual) {
      var diffMessage = GetDiffMessage(expected, actual);
      if (diffMessage != null) {
        throw new AssertActualExpectedException(expected, actual, diffMessage);
      }
    }
  }
}
