using System;
using System.IO;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForTopLevelDeclarations")]
public class FormatterIssues([NotNull] ITestOutputHelper output) : FormatterBaseTest(output) {
  [Fact]
  public async Task GitIssue4269FormatLemmaIde() {
    await FormatterWorksFor(@"
module Foo {
  lemma Bar(t: string)
  {

  }
}
");
  }

  [Fact]
  public async Task GitIssue4269BFormatMapIde() {
    await FormatterWorksFor(@"
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
  public async Task GitIssue3912FormatterCollectionArrow() {
    await FormatterWorksFor(@"
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
  public async Task GitIssue3912FormatterCollectionArrowA() {
    await FormatterWorksFor(@"
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
  public async Task GitIssue3912FormatterCollectionArrowB() {
    await FormatterWorksFor(@"
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
  public async Task GitIssue3912FormatterCollectionArrowC() {
    await FormatterWorksFor(@"
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
  public async Task GitIssue3960FormattingIssueForallStatements() {
    await FormatterWorksFor(@"
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
  public async Task GitIssue3944FormatterArgumentsDefaultValue() {
    await FormatterWorksFor(@"
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
  public async Task GitIssue3790DafnyFormatterProducesIncorrectIndentation() {
    await FormatterWorksFor(@"
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
  public async Task FormatterWorksForEmptyDocument() {
    await FormatterWorksFor(@"
", null, true);
  }
}