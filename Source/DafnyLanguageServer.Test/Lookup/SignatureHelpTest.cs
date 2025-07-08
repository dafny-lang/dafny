﻿using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  public class SignatureHelpTest : ClientBasedLanguageServerTest {

    [ItemCanBeNull]
    private async Task<SignatureHelp> RequestSignatureHelpAsync(TextDocumentItem documentItem, Position position, bool allowNull = false) {
      // TODO at this time we do not set the context since it appears that's also the case when used within VSCode.
      var result = await client.RequestSignatureHelp(
        new SignatureHelpParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      );
      if (result == null && !allowNull) {
        var diagnostics = await GetLastDiagnostics(documentItem);
        await output.WriteLineAsync($"diagnostics: {diagnostics.Stringify()}");
        Assert.NotNull(result);
      }
      return result;
    }

    [Fact]
    public async Task SignatureHelpForUnloadedDocumentReturnsNull() {
      var documentItem = CreateTestDocument("", "SignatureHelpForUnloadedDocumentReturnsNull.dfy");
      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (7, 11), true);
      Assert.Null(signatureHelp);
    }

    [Fact]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureForExistingMethod() {
      var source = @"
method Multiply(x: int, y: int) returns (p: int)
  ensures p == x * y
{
  return x * y;
}

method Main() {
  //
}".TrimStart();
      var documentItem = CreateTestDocument(source, "SignatureHelpOnOpeningParenthesesReturnsSignatureForExistingMethod.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((7, 2), (7, 2)),
          "Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (7, 11));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.Single(signatures);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.Equal(MarkupKind.Markdown, markup.Kind);
      Assert.Equal("```dafny\nmethod Multiply(x: int, y: int) returns (p: int)\n```", markup.Value);
    }

    [Fact]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureForExistingFunction() {
      var source = @"
function Multiply(x: int, y: int): int
{
  x * y
}

method Main() {
  //
}".TrimStart();
      var documentItem = CreateTestDocument(source, "SignatureHelpOnOpeningParenthesesReturnsSignatureForExistingFunction.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((6, 2), (6, 2)),
          "Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (6, 11));
      Assert.NotNull(signatureHelp);
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.Single(signatures);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.Equal(MarkupKind.Markdown, markup.Kind);
      Assert.Equal("```dafny\nfunction Multiply(x: int, y: int): int\n```", markup.Value);
    }

    [Fact]
    public async Task SignatureHelpOnOpeningParenthesesReturnsNullIfNoSuchMethodOrFunctionExists() {
      var source = @"
method Main() {
  //
}".TrimStart();
      var documentItem = CreateTestDocument(source, "SignatureHelpOnOpeningParenthesesReturnsNullIfNoSuchMethodOrFunctionExists.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((1, 2), (1, 2)),
          "Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (1, 11), true);
      Assert.Null(signatureHelp);
    }

    [Fact]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureOfClosestFunction() {
      var source = @"
function Multiply(x: int, y: int): int
{
  x * y
}

module Mod {
  function Multiply(a: int, b: int): int
  {
    a * b
  }

  class SomeClass {
    function Multiply(n: int, m: int): int
    {
      n * m
    }

    method GetProduct(x: int, y: int) returns (p: int)
      ensures p == x * y
    {
      //
    }
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source, "SignatureHelpOnOpeningParenthesesReturnsSignatureOfClosestFunction.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((20, 6), (20, 6)),
          "Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (20, 15));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.Single(signatures);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.Equal(MarkupKind.Markdown, markup.Kind);
      Assert.Equal("```dafny\nfunction SomeClass.Multiply(n: int, m: int): int\n```", markup.Value);
    }

    [Fact]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureOfClassMemberOfDesignator() {
      var source = @"
class A {
  constructor() {}

  function Multiply(n: int, m: int): int
  {
    n * m
  }
}


class B {
  var a: A;

  constructor() {
    a := new A();
  }

  function Multiply(x: int, y: int): int
  {
    x * y
  }

  method GetProduct(x: int, y: int) returns (p: int)
    ensures p == x * y
  {
    //
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source, "SignatureHelpOnOpeningParenthesesReturnsSignatureOfClassMemberOfDesignator.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(
        ref documentItem,
          new Range((25, 4), (25, 4)),
          "a.Multiply("
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (25, 15));
      Assert.NotNull(signatureHelp);
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.Single(signatures);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.Equal(MarkupKind.Markdown, markup.Kind);
      Assert.Equal("```dafny\nfunction A.Multiply(n: int, m: int): int\n```", markup.Value);
    }

    public SignatureHelpTest(ITestOutputHelper output) : base(output) {
    }
  }
}
