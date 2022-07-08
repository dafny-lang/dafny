using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

/// <summary>
/// This class tests whether editing a file results in
/// methods priorities for verification being set automatically.
/// </summary>
[TestClass]
public class ReorderingVerificationGutterStatusTester : LinearVerificationGutterStatusTester {
  private const int MaxTestExecutionTimeMs = 10000;

  [TestMethod/*, Timeout(MaxTestExecutionTimeMs * 10)*/]
  public async Task EnsuresPriorityDependsOnEditing() {
    await TestPriorities(@"
method m1() {
  assert fib(30) == 0;//Next2:  assert fib(30) == 0;
}
method m2() {
  assert fib(30) == 0;//Next1:  assert fib(30) == 0;
}
function fib(n: nat): nat {
  if (n <= 1) then n else fib(n - 1) + fib(n - 2)
}
",
      "m1 m2 fib\n" +
      "m2 m1 fib\n" +
      "m1 m2 fib"
    );
  }

  [TestMethod]
  public async Task EnsuresPriorityDependsOnEditingWhileEditingSameMethod() {
    await TestPriorities(@"
method m1() {
  assert fib(30) == 55;//Next7:  assert  fib(30) == 55;//Next8:  assert fib(30) == 55;
}
method m2() {
  assert fib(30) == 55;//Next5:  assert  fib(30) == 55;
}
method m3() {
  assert fib(30) == 55;//Next2:  assert  fib(30) == 55;//Next9:  assert fib(30) == 55;
}
method m4() {
  assert fib(30) == 55;//Next3:  assert  fib(30) == 55;//Next4:  assert fib(30) == 55;
}
method m5() {
  assert fib(30) == 55;//Next1:  assert  fib(30) == 55;//Next6:  assert fib(30) == 55;//Next10:  assert  fib(30) == 55;
}
function fib(n: nat): nat {
  if (n <= 1) then n else fib(n - 1) + fib(n - 2)
}
", "m1 m2 m3 m4 m5 fib\n" +
      "m5 m1 m2 m3 m4 fib\n" +
      "m3 m5 m1 m2 m4 fib\n" +
      "m4 m3 m5 m1 m2 fib\n" +
      "m4 m3 m5 m1 m2 fib\n" +
      "m2 m4 m3 m5 m1 fib\n" +
      "m5 m2 m4 m3 m1 fib\n" +
      "m1 m5 m2 m4 m3 fib\n" +
      "m1 m5 m2 m4 m3 fib\n" +
      "m3 m1 m5 m2 m4 fib\n" +
      "m5 m3 m1 m2 m4 fib"
    );
  }

  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethods() {
    await TestPriorities(@"
method m1() { assert fib(30) == 55; }
method m2() { assert fib(30) == 55; }
method m3() {
  assert fib(30) == 55;//Next1:  assert  fib(30) == 55;
} 
method m4() {
  assert fib(30) == 55;//Next2:  assert  fib(30) == 55;
}
function fib(n: nat): nat {
  if (n <= 1) then n else fib(n - 1) + fib(n - 2)
}
method m5() { assert fib(30) == 55; } //Remove3:
",
    "m1 m2 m3 m4 fib m5\n" +
    "m3 m1 m2 m4 fib m5\n" +
    "m4 m3 m1 m2 fib m5\n" +
    "m1 m2 m3 m4 fib");
  }


  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethodsWhileTypo() {
      await TestPriorities(@"
method m1() { assert fib(30) == 55; }
method m2() {
  assert fib(30) == 55;//Next3:  typo//Next5:  assert fib(30) == 55;
}
method m3() {
  assert fib(30) == 55;//Next1:  assert  fib(30) == 55;
} 
method m4() {
  assert fib(30) == 55;//Next2:  assert  fib(30) == 55;
}
function fib(n: nat): nat {
  if (n <= 1) then n else fib(n - 1) + fib(n - 2)
}
method m5() { assert fib(30) == 55; } //Remove4:
",
      "m1 m2 m3 m4 fib m5\n" +
      "m3 m1 m2 m4 fib m5\n" +
      "m4 m3 m1 m2 fib m5\n" +
      "null\n" +
      "m1 m2 m3 m4 fib\n" +
      "m2 m4 m3 m1 fib"
    );
  }

  // Requires changes to not change the position of symbols for now, as we are not applying the changes to the local code for now.
  private async Task TestPriorities(string codeAndChanges, string symbolsString) {
    var symbols = ExtractSymbols(symbolsString);
    await SetUp(new Dictionary<string, string> {
    { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" },
    });

    var (code, changes) = ExtractCodeAndChanges(codeAndChanges.TrimStart());
    var documentItem = CreateTestDocument(code);
    client.OpenDocument(documentItem);

    var initialOrder = await GetFlattenedPositionOrder(CancellationToken);
    var initialSymbols = GetSymbols(code, initialOrder).ToList();
    Assert.IsTrue(symbols.First().SequenceEqual(initialSymbols),
      $"Expected {string.Join(", ", symbols.First())} but got {string.Join(", ", initialSymbols)}");
    foreach (var (change, expectedSymbols) in changes.Zip(symbols.Skip(1))) {
      ApplyChange(ref documentItem, change.changeRange, change.changeValue);
      if (expectedSymbols != null) {
        var orderAfterChange = await GetFlattenedPositionOrder(CancellationToken);
        var orderAfterChangeSymbols = GetSymbols(code, orderAfterChange).ToList();
        Assert.IsTrue(expectedSymbols.SequenceEqual(orderAfterChangeSymbols),
          $"Expected {string.Join(", ", expectedSymbols)} but got {string.Join(", ", orderAfterChangeSymbols)}." +
          $"\nHistory was: {string.Join("\n", verificationStatusReceiver.History)}");
      }
    }
  }

  private IEnumerable<string> GetSymbols(string code, List<Position> positions) {
    var lines = code.Split("\n");
    return positions.Select(position => {
      var line = lines[position.Line];
      var word = line.Skip(position.Character).TakeWhile(c => !char.IsPunctuation(c)).ToArray();
      return new string(word);
    });
  }

  private static List<List<string>> ExtractSymbols(string symbolsString) {
    return symbolsString.Split("\n")
      .Select(array => array == "null" ? null : array.Split(" ").ToList()).ToList();
  }

  private async Task<List<Position>> GetFlattenedPositionOrder(CancellationToken cancellationToken) {
    return (await GetRunningOrder(cancellationToken).ToListAsync(cancellationToken)).
      SelectMany(r => r).
      Select(r => r.Start).ToList();
  }

  [TestCleanup]
  public void Cleanup() {
    DafnyOptions.Install(DafnyOptions.Create());
  }
}