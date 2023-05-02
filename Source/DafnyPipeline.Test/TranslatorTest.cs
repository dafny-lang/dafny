using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using Microsoft.CodeAnalysis;
using Bpl = Microsoft.Boogie;
using Xunit;
using Microsoft.Dafny;
using Microsoft.Dafny.ProofObligationDescription;

namespace DafnyPipeline.Test;

[Collection("Dafny translator tests")]
public class TranslatorTest {

  private void Expect(Bpl.Expr expr, bool isAlwaysTrue, bool isAlwaysFalse) {
    Assert.Equal(isAlwaysTrue, Translator.IsExprAlways(expr, true));
    Assert.Equal(isAlwaysFalse, Translator.IsExprAlways(expr, false));
  }

  [Fact]
  public void EnsuresIsAlwaysOptimizedCorrectly() {
    var @true = new Bpl.LiteralExpr(Bpl.Token.NoToken, true);
    const bool yes = true;
    const bool no = false;
    Bpl.IToken nt = Bpl.Token.NoToken;
    Expect(@true, isAlwaysTrue: yes, isAlwaysFalse: no);

    var @false = new Bpl.LiteralExpr(nt, false);
    Expect(@false, isAlwaysTrue: no, isAlwaysFalse: yes);

    var var = new Bpl.IdentifierExpr(nt, "v");
    Expect(var, isAlwaysTrue: no, isAlwaysFalse: no);

    Expect(Bpl.Expr.Imp(@true, var), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.Imp(@false, var), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Imp(var, @true), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Imp(var, @false), isAlwaysTrue: no, isAlwaysFalse: no);

    Expect(Bpl.Expr.And(@true, var), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.And(@false, var), isAlwaysTrue: no, isAlwaysFalse: yes);
    Expect(Bpl.Expr.And(var, @true), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.And(var, @false), isAlwaysTrue: no, isAlwaysFalse: yes);

    Expect(Bpl.Expr.Or(@true, var), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Or(@false, var), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.Or(var, @true), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Or(var, @false), isAlwaysTrue: no, isAlwaysFalse: no);

    Expect(Bpl.Expr.Not(@true), isAlwaysTrue: no, isAlwaysFalse: yes);
    Expect(Bpl.Expr.Not(@false), isAlwaysTrue: yes, isAlwaysFalse: no);

    var forallTrue = new Bpl.ForallExpr(nt, new List<Bpl.TypeVariable>(), new List<Bpl.Variable>(), @true);
    var forallFalse = new Bpl.ForallExpr(nt, new List<Bpl.TypeVariable>(), new List<Bpl.Variable>(), @false);

    Expect(forallTrue, isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(forallFalse, isAlwaysTrue: no, isAlwaysFalse: no);

    var existsTrue = new Bpl.ExistsExpr(nt, new List<Bpl.Variable>(), @true);
    var existsFalse = new Bpl.ExistsExpr(nt, new List<Bpl.Variable>(), @false);

    Expect(existsFalse, isAlwaysTrue: no, isAlwaysFalse: yes);
    Expect(existsTrue, isAlwaysTrue: no, isAlwaysFalse: no);

    var forallFalseImpliesSomething = new Bpl.ForallExpr(nt, new List<Bpl.TypeVariable>(), new List<Bpl.Variable>(), Bpl.Expr.Imp(@false, var));
    Expect(forallFalseImpliesSomething, isAlwaysTrue: yes, isAlwaysFalse: no);
  }

  // Test of embedding code into proof obligation descriptions

  private void ShouldHaveImplicitCode(string program, string expected, DafnyOptions options = null) {
    if (program.IndexOf("// Here", StringComparison.Ordinal) == -1) {
      Assert.Fail("Test is missing // Here");
    }
    var expectedLine = program.Split("// Here")[0].Count(c => c == '\n') + 1;
    Microsoft.Dafny.Type.ResetScopes();
    options = options ?? new DafnyOptions();
    BatchErrorReporter reporter = new BatchErrorReporter(options);
    var builtIns = new BuiltIns(options);
    var module = new LiteralModuleDecl(new DefaultModuleDefinition(), null);
    Parser.Parse(program, "virtual", "virtual", module, builtIns, reporter);
    if (reporter.ErrorCount > 0) {
      var error = reporter.AllMessages[ErrorLevel.Error][0];
      Assert.False(true, $"{error.Message}: line {error.Token.line} col {error.Token.col}");
    }
    var dafnyProgram = new Program("programName", module, builtIns, reporter);
    Main.Resolve(dafnyProgram, reporter);
    if (reporter.ErrorCount > 0) {
      var error = reporter.AllMessages[ErrorLevel.Error][0];
      Assert.False(true, $"{error.Message}: line {error.Token.line} col {error.Token.col}");
    }

    var engine = Bpl.ExecutionEngine.CreateWithoutSharedCache(options);
    var boogiePrograms = DafnyDriver.Translate(engine.Options, dafnyProgram).ToList();
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
                var str = Printer.ExprToString(options, assertedExpr);
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

  // Test of embedding code into proof obligation descriptions

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
predicate P(x: int)
 
function Test(x: int, z: int): int
  requires P(z) && x <= z
{
  var b, c :| x <= b && b <= c && P(c); // Here
  b
}
", "forall b: int, c: int, b': int, c': int | x <= b && b <= c && P(c) && x <= b' && b' <= c' && P(c') :: b == b' && c == c'");
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
}
