using Xunit;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForTopLevelDeclarations")]
public class FormatterIssues : FormatterBaseTest {
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
}