using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Bpl = Microsoft.Boogie;
using Xunit;
using Microsoft.Dafny;

namespace DafnyPipeline.Test;

[Collection("Dafny implicit assertion test")]
public class ImplicitAssertionTest {
  [Fact]
  public async Task GitIssue4016ExplicitAssertionPrintNested() {
    await ShouldHaveImplicitCode(@"
datatype D = C(value: int) | N

function Test(e: D, inputs: map<int, int>): bool {
  match e
  case N => true
  case C(index) => inputs[index] == index // Here
}",
    "index in inputs"
);
  }

  [Fact]
  public async Task DivisionByZero() {
    await ShouldHaveImplicitCode(@"
method Test(x: int, y: int) returns (z: int) {
  z := 2 / (x + y); // Here
}
", "x + y != 0");
  }

  [Fact]
  public async Task CompilableAssignSuchThat() {
    await ShouldHaveImplicitCode(@"
predicate P(x: int, c: int)
 
function Test(x: int, z: int): int
  requires P(x, z) && x <= z
{
  var b, c :| x <= b && P(b, c); // Here
  b
}
", "forall b: int, c: int, b': int, c': int | x <= b && P(b, c) && x <= b' && P(b', c') :: b == b' && c == c'");
  }

  [Fact]
  public async Task AssignmentSuchThatShouldExist() {
    await ShouldHaveImplicitCode(@"
predicate P(x: int)
 
lemma PUnique(a: int)
  ensures forall x, y | a <= x && a <= y :: P(x) == P(y) ==> x == y

function Test(x: int): int
{
  PUnique(x);
  var b :| x <= b && P(b); // Here
  b
}
", "exists b: int :: x <= b && P(b)");
  }

  [Fact]
  public async Task SeqIndexOutOfRange() {
    await ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int) {
  var b := a(2)[i + 3]; // Here
}
", "0 <= i + 3 < |a(2)|");
  }

  [Fact]
  public async Task SeqIndexOutOfRangeUpdate() {
    await ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int) {
  var b := a(2)[i + 3 := 1]; // Here
}
", "0 <= i + 3 < |a(2)|");
  }

  [Fact]
  public async Task SeqSliceLowerOutOfRange() {
    await ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int) {
  var b := a(2)[i + 3..]; // Here
}
", "0 <= i + 3 <= |a(2)|");
  }

  [Fact]
  public async Task SeqUpperOutOfRange() {
    await ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int, j: int) {
  var b := a(2)[j..i + 3]; // Here
}
", "j <= i + 3 <= |a(2)|");
  }

  [Fact]
  public async Task ArrayIndexOutOfRange() {
    await ShouldHaveImplicitCode(@"
method Test(a: int -> array<int>, i: int) {
  var b := a(2)[i + 3]; // Here
}
", "0 <= i + 3 < a(2).Length");
  }

  [Fact]
  public async Task ArrayIndex0OutOfRange() {
    await ShouldHaveImplicitCode(@"
method Test(a: int -> array2<int>, i: int) {
  var b := a(2)[i + 3, i + 4]; // Here
}
", "0 <= i + 3 < a(2).Length0");
  }

  [Fact]
  public async Task ArrayIndex1OutOfRange() {
    await ShouldHaveImplicitCode(@"
method Test(a: int -> array2<int>, i: int) {
  var b := a(2)[i + 3, i + 4]; // Here
}
", "0 <= i + 4 < a(2).Length1");
  }

  [Fact]
  public async Task ElementNotInDomain() {
    await ShouldHaveImplicitCode(@"
method Test(m: map<int, int>, x: int) {
  var b := m[x + 2]; // Here
}
", "x + 2 in m");
  }
  /** Look at the line containing "// Here", and for every assertion there,
  look if they contain an implicit assertion that, if printed,
  would generate the string "expected" */
  private async Task ShouldHaveImplicitCode(string program, string expected, DafnyOptions options = null) {
    if (program.IndexOf("// Here", StringComparison.Ordinal) == -1) {
      Assert.Fail("Test is missing // Here");
    }
    var expectedLine = program.Split("// Here")[0].Count(c => c == '\n') + 1;
    Microsoft.Dafny.Type.ResetScopes();
    options = options ?? new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    var uri = new Uri("virtual:///virtual");
    BatchErrorReporter reporter = new BatchErrorReporter(options);
    var parseResult = await new ProgramParser().Parse(program, uri, reporter);
    var dafnyProgram = parseResult.Program;
    if (reporter.HasErrors) {
      var error = reporter.AllMessagesByLevel[ErrorLevel.Error][0];
      Assert.False(true, $"{error.Message}: line {error.Token.line} col {error.Token.col}");
    }
    DafnyMain.Resolve(dafnyProgram);
    if (reporter.HasErrors) {
      var error = reporter.AllMessagesByLevel[ErrorLevel.Error][0];
      Assert.False(true, $"{error.Message}: line {error.Token.line} col {error.Token.col}");
    }

    var boogiePrograms = SynchronousCliCompilation.Translate(options, dafnyProgram).ToList();
    Assert.Single(boogiePrograms);
    var boogieProgram = boogiePrograms[0].Item2;
    var encountered = new List<string>();
    var found = false;
    foreach (var implementation in boogieProgram.Implementations) {
      foreach (var block in implementation.Blocks) {
        foreach (var cmd in block.Cmds) {
          if (cmd is Bpl.AssertCmd { tok: { line: var line } } assertCmd && line == expectedLine) {
            if (assertCmd.Description is ProofObligationDescription description) {
              var assertedExpr = description.GetAssertedExpr(options);
              if (assertedExpr != null) {
                var str = Printer.ExprToString(options, assertedExpr, new PrintFlags(UseOriginalDafnyNames: true));
                if (str == expected) {
                  found = true;
                } else {
                  encountered.Add(str);
                }
              }
            }
          }
        }
      }
    }

    if (!found) {
      if (encountered.Count > 0) {
        Assert.Fail($"Expected {expected}, but only encountered {(string.Join(",", encountered))}");
      } else {
        Assert.Fail($"Did not find {expected}");
      }
    }
  }

}
