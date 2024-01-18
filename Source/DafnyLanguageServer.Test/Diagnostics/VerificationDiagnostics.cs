using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Castle.Core.Logging;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

public class VerificationDiagnostics : ClientBasedLanguageServerTest {

  [Fact]
  public async Task BadSolverPath() {
    var projectFile = @"
[options]
solver-path=""doesNotExist""
";
    var program = @"
method Foo() ensures false { }";
    var path = Path.GetRandomFileName();
    CreateAndOpenTestDocument(projectFile, Path.Combine(path, DafnyProject.FileName));
    var document = CreateAndOpenTestDocument(program, Path.Combine(path, "BadSolverPath.dfy"));
    var diagnostics = await GetLastDiagnostics(document);
    Assert.Contains(diagnostics, d => d.Message.Contains("Cannot find specified prover"));
  }

  [Fact]
  public async Task Iterator() {
    var program = @"

class List<T> {
  ghost var Contents: seq<T>
  ghost var Repr: set<object>

  var a: array<T>
  var n: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    a in Repr &&
    n <= a.Length &&
    Contents == a[..n]
  }

  constructor Init()
    ensures Valid() && fresh(Repr)
    ensures Contents == []
  {
    Contents, n := [], 0;
    a := new T[0];
    Repr := {this, a};
  }

  method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents) + [t]
  {
    if (n == a.Length) {
      var b := new T[2 * a.Length + 1](i requires 0 <= i reads this, a =>
                                       if i < a.Length then a[i] else t);
      assert b[..n] == a[..n] == Contents;
      a, Repr := b, Repr + {b};
      assert b[..n] == Contents;
    }
    a[n], n, Contents := t, n + 1, Contents + [t];
  }
}

class Cell { var data: int }

iterator M<T(0)>(l: List<T>, c: Cell) yields (x: T)
  requires l.Valid()
  reads l.Repr
  modifies c
  yield requires true
  yield ensures xs <= l.Contents  // this is needed in order for the next line to be well-formed
  yield ensures x == l.Contents[|xs|-1]
  ensures xs == l.Contents
{
  var i := 0;
  while i < l.n
    invariant i <= l.n && i == |xs| && xs <= l.Contents
  {
    if (*) { assert l.Valid(); }  // this property is maintained, due to the reads clause
    if (*) {
      x := l.a[i]; yield;  // or, equivalently, 'yield l.a[i]'
      i := i + 1;
    } else {
      x, i := l.a[i], i + 1;
      yield;
    }
  }
}";
    var document = CreateAndOpenTestDocument(program, "ErrorLimitReached.dfy");
    await WaitUntilAllStatusAreCompleted(document);
  }

  [Fact]
  public async Task ErrorLimitReached() {
    var source = @"
method ErrorLimitReached(x: int) {
  assert x > 0;
  assert x > 1;
  assert x > 2;
  assert x > 3;
  assert x > 4;
  assert x > 5;
  if (*) {
    assert false;
  } else {
    var x := 3 / 2;
  }
}".TrimStart();
    var document = CreateAndOpenTestDocument(source, "ErrorLimitReached.dfy");
    var diagnostics = await GetLastDiagnostics(document);
    Assert.Contains(diagnostics, d => d.Message.Contains("Verification hit error limit"));
  }

  [Fact]
  public async Task ShowImplicitAssertions() {
    await SetUp(o => o.Set(CommonOptionBag.ShowAssertions, CommonOptionBag.AssertionShowMode.Implicit));

    var source = @"
method ImplicitAssertions(x: int) {
  if (*) {
    assert false;
  } else {
    var x := 3 / 2;
  }
}".TrimStart();
    var document = CreateAndOpenTestDocument(source, "ErrorLimitReached.dfy");
    var diagnostics = await GetLastDiagnostics(document, DiagnosticSeverity.Hint);
    Assert.Contains(diagnostics, d => d.Message.Contains("Implicit assertion: non-zero divisor")
                                      && d.Range == new Range(4, 15, 4, 16));
    Assert.DoesNotContain(diagnostics, d => d.Message.Contains("Explicit assertion: assert statement"));
  }

  [Fact]
  public async Task ShowAllAssertions() {
    await SetUp(o => o.Set(CommonOptionBag.ShowAssertions, CommonOptionBag.AssertionShowMode.All));

    var source = @"
method ImplicitAssertions(x: int) {
  if (*) {
    assert false;
  } else {
    var x := 3 / 2;
  }
}".TrimStart();
    var document = CreateAndOpenTestDocument(source, "ErrorLimitReached.dfy");
    var diagnostics = await GetLastDiagnostics(document, DiagnosticSeverity.Hint);
    Assert.Contains(diagnostics, d => d.Message.Contains("Implicit assertion: non-zero divisor"));
    Assert.Contains(diagnostics, d => d.Message.Contains("Explicit assertion: assert statement") && d.Range == new Range(2, 11, 2, 16));
  }

  public VerificationDiagnostics(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}