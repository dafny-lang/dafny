using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForTopLevelDeclarations")]
public class FormatterIssues : FormatterBaseTest {
  [Fact]
  public void GitIssue3944FormatterArgumentsDefaultValue() {
    FormatterWorksFor(@"
function Example(
  newNames : map<string, string> := map[],
  a: int
) : bool
{
  true
}
");
  }

  [Fact]
  public void GitIssue3790DafnyFormatterProducesIncorrectIndentation() {
    FormatterWorksFor(@"
lemma Try(i: int)
{
  match i {
    case i' =>
      var x :| x == i';
      assert x == i';
  }
}");
  }

  [Fact]
  public void FormatterWorksForEmptyDocument() {
    FormatterWorksFor(@"
", null, true);
  }

  public FormatterIssues([NotNull] ITestOutputHelper output) : base(output) {
  }
}