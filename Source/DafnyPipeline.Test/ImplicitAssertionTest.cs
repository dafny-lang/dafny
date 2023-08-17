using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Bpl = Microsoft.Boogie;
using Xunit;
using Microsoft.Dafny;
using Microsoft.Dafny.ProofObligationDescription;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Dafny implicit assertion test")]
public class ImplicitAssertionTest {
  [Fact]
  public void GitIssue4016ExplicitAssertionPrintNested() {
    ShouldHaveImplicitCode(@"
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
  public void DivisionByZero() {
    ShouldHaveImplicitCode(@"
method Test(x: int, y: int) returns (z: int) {
  z := 2 / (x + y); // Here
}
", "x + y != 0");
  }

  [Fact]
  public void CompilableAssignSuchThat() {
    ShouldHaveImplicitCode(@"
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
  public void AssignmentSuchThatShouldExist() {
    ShouldHaveImplicitCode(@"
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
  public void SeqIndexOutOfRange() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int) {
  var b := a(2)[i + 3]; // Here
}
", "0 <= i + 3 < |a(2)|");
  }

  [Fact]
  public void SeqIndexOutOfRangeUpdate() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int) {
  var b := a(2)[i + 3 := 1]; // Here
}
", "0 <= i + 3 < |a(2)|");
  }

  [Fact]
  public void SeqSliceLowerOutOfRange() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int) {
  var b := a(2)[i + 3..]; // Here
}
", "0 <= i + 3 <= |a(2)|");
  }

  [Fact]
  public void SeqUpperOutOfRange() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> seq<int>, i: int, j: int) {
  var b := a(2)[j..i + 3]; // Here
}
", "j <= i + 3 <= |a(2)|");
  }

  [Fact]
  public void ArrayIndexOutOfRange() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> array<int>, i: int) {
  var b := a(2)[i + 3]; // Here
}
", "0 <= i + 3 < a(2).Length");
  }

  [Fact]
  public void ArrayIndex0OutOfRange() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> array2<int>, i: int) {
  var b := a(2)[i + 3, i + 4]; // Here
}
", "0 <= i + 3 < a(2).Length0");
  }

  [Fact]
  public void ArrayIndex1OutOfRange() {
    ShouldHaveImplicitCode(@"
method Test(a: int -> array2<int>, i: int) {
  var b := a(2)[i + 3, i + 4]; // Here
}
", "0 <= i + 4 < a(2).Length1");
  }

  [Fact]
  public void ElementNotInDomain() {
    ShouldHaveImplicitCode(@"
method Test(m: map<int, int>, x: int) {
  var b := m[x + 2]; // Here
}
", "x + 2 in m");
  }
  /** Look at the line containing "// Here", and for every assertion there,
  look if they contain an implicit assertion that, if printed,
  would generate the string "expected" */
  private void ShouldHaveImplicitCode(string program, string expected, DafnyOptions options = null) {
    if (program.IndexOf("// Here", StringComparison.Ordinal) == -1) {
      Assert.Fail("Test is missing // Here");
    }
    var expectedLine = program.Split("// Here")[0].Count(c => c == '\n') + 1;
    Microsoft.Dafny.Type.ResetScopes();
    options = options ?? new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
    var uri = new Uri("virtual:///virtual");
    BatchErrorReporter reporter = new BatchErrorReporter(options);
    var dafnyProgram = new ProgramParser().Parse(program, uri, reporter);
    if (reporter.ErrorCount > 0) {
      var error = reporter.AllMessagesByLevel[ErrorLevel.Error][0];
      Assert.False(true, $"{error.Message}: line {error.Token.line} col {error.Token.col}");
    }
    DafnyMain.Resolve(dafnyProgram);
    if (reporter.ErrorCount > 0) {
      var error = reporter.AllMessagesByLevel[ErrorLevel.Error][0];
      Assert.False(true, $"{error.Message}: line {error.Token.line} col {error.Token.col}");
    }

    var boogiePrograms = DafnyDriver.Translate(options, dafnyProgram).ToList();
    Assert.Single(boogiePrograms);
    var boogieProgram = boogiePrograms[0].Item2;
    var encountered = new List<string>();
    var found = false;
    foreach (var implementation in boogieProgram.Implementations) {
      foreach (var block in implementation.Blocks) {
        foreach (var cmd in block.cmds) {
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
