using System.Text;
using DiffPlex.DiffBuilder;
using DiffPlex.DiffBuilder.Model;
using Xunit;
using XunitAssertMessages;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class AssertWithDiff {
  public static void Equal(string expected, string actual) {
    var diff = InlineDiffBuilder.Instance.BuildDiffModel(expected, actual);
    if (!diff.HasDifferences) {
      return;
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

    AssertM.Equal(expected, actual, message.ToString());
  }
}
