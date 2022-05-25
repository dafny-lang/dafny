using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class DiagnosticsTest : ClientBasedLanguageServerTest {
    private IDictionary<string, string> configuration;

    public async Task SetUp(IDictionary<string, string> configuration) {
      this.configuration = configuration;
      await SetUp();
    }

    protected override IConfiguration CreateConfiguration() {
      return configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(configuration).Build();
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentReportsEmptyDiagnostics() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(0, diagnostics.Length);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithSyntaxErrorReportsDiagnosticsWithParserErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithSemanticErrorReportsDiagnosticsWithSemanticErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - ""1"");
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Resolver", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithMultipleSemanticErrorsReportsDiagnosticsWithAllSemanticErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == ""0"" {
    product := 0;
  } else {
    var step := Multiply(x, y - ""1"");
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(2, diagnostics.Length);
      Assert.AreEqual("Resolver", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual("Resolver", diagnostics[1].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[1].Severity);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithVerificationErrorReportsDiagnosticsWithVerificationErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual(MessageSource.Verifier.ToString(), diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithVerificationErrorDoesNotReportDiagnosticsWithVerificationErrorsIfNotVerifyOnChange() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(0, diagnostics.Length);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithMultipleVerificationErrorsReportsDiagnosticsWithAllVerificationErrorsAndRelatedInformation() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(2, diagnostics.Length);
      Assert.AreEqual(MessageSource.Verifier.ToString(), diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(MessageSource.Verifier.ToString(), diagnostics[1].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[1].Severity);
      Assert.AreEqual(1, diagnostics[0].RelatedInformation.Count());
      var relatedInformation = diagnostics[0].RelatedInformation.First();
      Assert.AreEqual("This is the postcondition that might not hold.", relatedInformation.Message);
      Assert.AreEqual(new Range(new Position(2, 30), new Position(2, 42)), relatedInformation.Location.Range);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithSyntaxErrorsReportsTheSyntaxErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnosticsAfterOpening = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 54)),
            Text = ""
          }
        }
      });

      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithSyntaxErrorsReportsTheSyntaxErrorsIfNotVerifyOnChange() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnosticsAfterOpening = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 54)),
            Text = ""
          }
        }
      });

      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithVerificationErrorsReportsTheVerificationErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnosticsAfterOpening = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((8, 30), (8, 31)),
            Text = "+"
          }
        }
      });

      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual(MessageSource.Verifier.ToString(), diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithVerificationErrorsDoesNotReportVerificationErrorsIfNotVerifyOnChange() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnosticsAfterOpening = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((8, 30), (8, 31)),
            Text = "+"
          }
        }
      });

      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task ApplyingMultipleChangesInDocumentOnlySendsOneReport() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnosticsAfterOpening = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      var newVersion = documentItem with { Version = documentItem.Version + 1 };
      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = newVersion.Uri,
          Version = newVersion.Version
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 54)),
            Text = ""
          },
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 53)),
            Text = ")"
          }
        }
      });

      // The test applies a change that introduces a syntax error and fixes it thereafter.
      // Therefore, we know that the erroneous state was never reported when we now receive
      // a report without any diagnostics/errors.
      // Otherwise, we'd have to wait for a signal/diagnostic that should never be sent, e.g.
      // with a timeout.
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task ClosingDocumentWithSyntaxErrorHidesDiagnosticsBySendingEmptyDiagnostics() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      client.DidCloseTextDocument(new DidCloseTextDocumentParams { TextDocument = documentItem });
      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(0, diagnostics.Length);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentThatIncludesNonExistentDocumentReportsParserErrorAtInclude() {
      var source = "include \"doesNotExist.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 26)), diagnostics[0].Range);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentThatIncludesDocumentWithSyntaxErrorsReportsParserErrorAtInclude() {
      var source = "include \"syntaxError.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 25)), diagnostics[0].Range);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentThatIncludesDocumentWithSemanticErrorsReportsResolverErrorAtInclude() {
      var source = "include \"syntaxError.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 25)), diagnostics[0].Range);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithSemanticErrorsInIncludeReportsResolverErrorAtIncludeStatement() {
      var source = "include \"semanticError.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Resolver", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 27)), diagnostics[0].Range);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task SavingDocumentWithVerificationErrorDoesNotDiscardDiagnosticsWithVerificationErrorsIfVerifyOnChange() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var changeDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(1, changeDiagnostics.Length);
      Assert.AreEqual(MessageSource.Verifier.ToString(), changeDiagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, changeDiagnostics[0].Severity);
      client.SaveDocument(documentItem);

      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task SavingDocumentWithVerificationErrorReportsDiagnosticsWithVerificationErrorsIfVerifyOnSave() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var changeDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(0, changeDiagnostics.Length);
      client.SaveDocument(documentItem);
      var saveDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, saveDiagnostics.Length);
      Assert.AreEqual(MessageSource.Verifier.ToString(), saveDiagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, saveDiagnostics[0].Severity);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithVerificationErrorReportsDiagnosticsWithVerificationErrorsAndNestedRelatedLocations() {
      var source = @"
class Test {
    var a: nat
    var b: nat
    var c: nat

    predicate Valid()
        reads this
    {
        && a < b
        && b < c
    }

    method Foo()
        requires Valid()
        ensures Valid()
        modifies this
    {
        c := 10;
    }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual(MessageSource.Verifier.ToString(), diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      var relatedInformation = diagnostics[0].RelatedInformation.ToArray();
      Assert.AreEqual(2, relatedInformation.Length);
      Assert.AreEqual("This is the postcondition that might not hold.", relatedInformation[0].Message);
      Assert.AreEqual(new Range((14, 16), (14, 21)), relatedInformation[0].Location.Range);
      Assert.AreEqual("Related location", relatedInformation[1].Message);
      Assert.AreEqual(new Range((9, 11), (9, 16)), relatedInformation[1].Location.Range);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithMultipleVerificationCoresReturnsStableDiagnostics() {
      var sourceWithHighTimeout = new CancellationTokenSource();
      sourceWithHighTimeout.CancelAfter(TimeSpan.FromSeconds(240));
      var cancellationToken = sourceWithHighTimeout.Token;

      var source = @"
method t0() { assert true; }
method t1() { assert true; }
method t2() { assert true; }
method t3() { assert true; }
method t4() { assert true; }
method t5() { assert true; }
method t6() { assert false; }
method t7() { assert false; }
method t8() { assert false; }
method t9() { assert false; }
method t10() { assert false; }".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "4" }
      });
      for (int i = 0; i < 10; i++) {
        var documentItem = CreateTestDocument(source, $"test_{i}.dfy");
        client.OpenDocument(documentItem);
        var diagnostics = await GetLastDiagnostics(documentItem, cancellationToken);
        Assert.AreEqual(5, diagnostics.Length);
        Assert.AreEqual(MessageSource.Verifier.ToString(), diagnostics[0].Source);
        Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
        await AssertNoDiagnosticsAreComing(cancellationToken);
      }
    }

    [TestMethod]
    public async Task OpeningDocumentWithTimeoutReportsTimeoutDiagnostic() {
      var source = @"
function method {:unroll 100} Ack(m: nat, n: nat): nat
  decreases m, n
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

method test() {
  assert Ack(5, 5) == 0;
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.TimeLimit)}", "1" }
      });
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.IsTrue(diagnostics[0].Message.Contains("timed out"));
    }

    [TestMethod]
    public async Task OpeningDocumentWithComplexExpressionUnderlinesAllOfIt() {
      var source = @"
method test(i: int, j: int) {
  assert i > j || i < j; 
//       ^^^^^^^^^^^^^^
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual(MessageSource.Verifier.ToString(), diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((1, 9), (1, 23)), diagnostics[0].Range);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithFailedCallUnderlinesAllOfIt() {
      var source = @"
method test() {
  other(2, 1);
//     ^^^^^^^
}

method other(i: int, j: int)
  requires i < j {
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual(MessageSource.Verifier.ToString(), diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((1, 7), (1, 14)), diagnostics[0].Range);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningDocumentWithFailedCallExpressionUnderlinesAllOfIt() {
      var source = @"
method test() {
  var x := 1 + other(2, 1);
//             ^^^^^^^^^^
}

function method other(i: int, j: int): int
  requires i < j {
  2
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual(MessageSource.Verifier.ToString(), diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((1, 15), (1, 25)), diagnostics[0].Range);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task IncrementalVerificationDiagnosticsBetweenMethods() {
      var source = SlowToVerify + @"
method test() {
  assert false;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken.None, documentItem);
      Assert.AreEqual(0, resolutionDiagnostics.Length);
      var firstVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken.None, documentItem);
      var secondVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken.None, documentItem);

      Assert.AreEqual(1, firstVerificationDiagnostics.Length);
      // Second diagnostic is a timeout exception from SlowToVerify
      Assert.AreEqual(2, secondVerificationDiagnostics.Length);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task IncrementalVerificationDiagnosticsBetweenAssertionsAndWellFormedness() {
      var source = @"
method test() 
  ensures 3 / 0 == 1 {
  assert false;
}
".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" }
      });
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken.None, documentItem);
      Assert.AreEqual(0, resolutionDiagnostics.Length);
      var firstVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken.None, documentItem);
      var secondVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken.None, documentItem);

      Assert.AreEqual(1, firstVerificationDiagnostics.Length);
      Assert.AreEqual(2, secondVerificationDiagnostics.Length);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task NoIncrementalVerificationDiagnosticsBetweenAssertionBatches() {
      var source = @"
method test(x: int) {
  assert x != 2;
  assert {:split_here} true;
  assert x != 3;
}
".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" }
      });
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken.None, documentItem);
      Assert.AreEqual(0, resolutionDiagnostics.Length);
      var firstVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken.None, documentItem);

      Assert.AreEqual(2, firstVerificationDiagnostics.Length);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task NoDiagnosticFlickeringWhenIncremental() {
      var source = @"
method test() {
  assert false;
}
method test2() {
  assert false;
}
".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" }
      });
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      Assert.AreEqual(0, resolutionDiagnostics.Length);
      var firstVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      var secondVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      Assert.AreEqual(1, firstVerificationDiagnostics.Length);
      Assert.AreEqual(2, secondVerificationDiagnostics.Length);

      ApplyChange(ref documentItem, new Range((1, 9), (1, 14)), "true"); ;

      var resolutionDiagnostics2 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      AssertDiagnosticListsAreEqualBesidesMigration(secondVerificationDiagnostics, resolutionDiagnostics2);
      var firstVerificationDiagnostics2 = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(1, firstVerificationDiagnostics2.Length); // Still contains second failing method

      ApplyChange(ref documentItem, new Range((4, 9), (4, 14)), "true");

      var resolutionDiagnostics3 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      AssertDiagnosticListsAreEqualBesidesMigration(firstVerificationDiagnostics2, resolutionDiagnostics3);
      var secondVerificationDiagnostics3 = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(0, secondVerificationDiagnostics3.Length);

      await AssertNoDiagnosticsAreComing(CancellationToken);
    }


    [TestMethod]
    public async Task ApplyChangeBeforeVerificationFinishes() {
      var source = @"
method test() {
  assert false;
}
".TrimStart() + SlowToVerify;
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" }
      });
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      Assert.AreEqual(0, resolutionDiagnostics.Length);
      var firstVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      Assert.AreEqual(1, firstVerificationDiagnostics.Length);
      ApplyChange(ref documentItem, new Range((1, 9), (1, 14)), "true");

      var resolutionDiagnostics2 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      AssertDiagnosticListsAreEqualBesidesMigration(firstVerificationDiagnostics, resolutionDiagnostics2);
      var firstVerificationDiagnostics2 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      var secondVerificationDiagnostics2 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      Assert.AreEqual(0, firstVerificationDiagnostics2.Length); // Still contains second failing method
      Assert.AreEqual(1, secondVerificationDiagnostics2.Length);

      await AssertNoDiagnosticsAreComing(CancellationToken);
    }


    [TestMethod]
    public async Task DoNotMigrateDiagnosticsOfRemovedMethod() {
      var source = @"
method test() {
  assert false;
}
method test2() {
  assert false;
}
".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" }
      });
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      Assert.AreEqual(0, resolutionDiagnostics.Length);
      var firstVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      var secondVerificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      Assert.AreEqual(1, firstVerificationDiagnostics.Length);
      Assert.AreEqual(2, secondVerificationDiagnostics.Length);

      /*
       * New source becomes
       * method test() {
           assert false;
           assert false;
         }
       */
      ApplyChange(ref documentItem, new Range((2, 0), (4, 0)), "");

      var resolutionDiagnostics2 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);

      // Resolution diagnostics still contain those of the deleted method.
      AssertDiagnosticListsAreEqualBesidesMigration(secondVerificationDiagnostics, resolutionDiagnostics2);
      var firstVerificationDiagnostics2 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, documentItem);
      // The second assert doesn't create a separate error since it's hidden by the first one.
      // The diagnostics of test2 has not been migrated since test2 no longer exists.
      Assert.AreEqual(1, firstVerificationDiagnostics2.Length);

      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    private static void AssertDiagnosticListsAreEqualBesidesMigration(Diagnostic[] secondVerificationDiagnostics2,
      Diagnostic[] resolutionDiagnostics3) {
      Assert.AreEqual(secondVerificationDiagnostics2.Length, resolutionDiagnostics3.Length);
      foreach (var t in secondVerificationDiagnostics2.Zip(resolutionDiagnostics3)) {
        Assert.AreEqual(t.First.Message, t.Second.Message);
      }
    }

    [TestMethod]
    public async Task DiagnosticsInDifferentImplementationUnderOneNamedVerificationTask() {
      var source = @"
method test() 
  ensures 3 / 0 == 2 {
  assert false;
}
".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" }
      });
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(2, diagnostics.Length);
    }

    [TestMethod]
    public async Task MethodRenameDoesNotAffectMigration() {
      var source = @"
method Foo() {
  assert false;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      await GetLastDiagnostics(documentItem, CancellationToken);
      ApplyChange(ref documentItem, new Range(0, 7, 0, 10), "Bar");
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [TestMethod]
    public async Task ModuleRenameDoesNotAffectMigration() {
      var source = @"
module Foo {
  method Bar() {
    assert false;
  }
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      await GetLastDiagnostics(documentItem, CancellationToken);
      ApplyChange(ref documentItem, new Range(0, 7, 0, 10), "Zap");
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }
  }
}
