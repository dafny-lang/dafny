using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForTopLevelDeclarations")]
public class FormatterIssues : FormatterBaseTest {
  [Fact]
  public void GitIssue4269FormatLemmaIde() {
    FormatterWorksFor(@"
module Foo {
  lemma Bar(t: string)
  {

  }
}
");
  }

  [Fact]
  public void GitIssue4269BFormatMapIde() {
    FormatterWorksFor(@"
module Foo {
  method Bar(
    a: map<string, string>,
    b: map<string, string>,
    c: map<string, string>
  )
}
");
  }

  [Fact]
  public void GitIssue3912FormatterCollectionArrow() {
    FormatterWorksFor(@"
const i :=
  a in
    B + // Previously it was not indented
    C +
    D &&
  b in
    B +
    C
");
  }

  [Fact]
  public void GitIssue3912FormatterCollectionArrowA() {
    FormatterWorksFor(@"
const newline :=
  set
    i <-
      PartA +
      PartB +
      PartC,
    j <-
      PartD
    ::
      f(i,j)

const sameline :=
  set i <-
        PartA +
        PartB +
        PartC,
    j <-
      PartD
    ::
      f(i,j)

");
  }

  [Fact]
  public void GitIssue3912FormatterCollectionArrowB() {
    FormatterWorksFor(@"
const newlineOp :=
  set
    i
    <-
      PartA +
      PartB +
      PartC,
    j
    <-
      PartD
    ::
      f(i,j)

");
  }

  [Fact]
  public void GitIssue3912FormatterCollectionArrowC() {
    FormatterWorksFor(@"
const sameLineOp :=
  set i
    <-
      PartA +
      PartB +
      PartC,
    j
    <- PartD +
       PartE
    ::
      f(i,j)
");
  }

  [Fact]
  public void GitIssue3960FormattingIssueForallStatements() {
    FormatterWorksFor(@"
lemma Lemma()
{
  forall pd0: int
    | && true
      && (true
          && true)
      && true
    ensures true {
  }
}");
  }

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