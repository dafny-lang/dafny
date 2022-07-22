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
    await WithNoopSolver(async () => {
      await TestPriorities(@"
method m1() {
  assert fib(10) == 0;//Next2:  assert fib(10) == 0;
}
method m2() {
  assert fib(10) == 0;//Next1:  assert fib(10) == 0;
}
function fib(n: nat): nat {
  if (n <= 1) then n else fib(n - 1) + fib(n - 2)
}
",
        "m1 m2 fib\n" +
        "m2 m1 fib\n" +
        "m1 m2 fib"
        );
    });
  }

  [TestMethod]
  public async Task EnsuresPriorityDependsOnEditingWhileEditingSameMethod() {
    await WithNoopSolver(async () => {
      await TestPriorities(@"
method m1() {
  assert fib(10) == 55;//Next7:  assert  fib(10) == 55;//Next8:  assert fib(10) == 55;
}
method m2() {
  assert fib(10) == 55;//Next5:  assert  fib(10) == 55;
}
method m3() {
  assert fib(10) == 55;//Next2:  assert  fib(10) == 55;//Next9:  assert fib(10) == 55;
}
method m4() {
  assert fib(10) == 55;//Next3:  assert  fib(10) == 55;//Next4:  assert fib(10) == 55;
}
method m5() {
  assert fib(10) == 55;//Next1:  assert  fib(10) == 55;//Next6:  assert fib(10) == 55;//Next10:  assert  fib(10) == 55;
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
    });
  }

  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethods() {
    await WithNoopSolver(async () => {
      await TestPriorities(@"
method m1() { assert fib(10) == 55; }
method m2() { assert fib(10) == 55; }
method m3() {
  assert fib(10) == 55;//Next1:  assert  fib(10) == 55;
} 
method m4() {
  assert fib(10) == 55;//Next2:  assert  fib(10) == 55;
}
function fib(n: nat): nat {
  if (n <= 1) then n else fib(n - 1) + fib(n - 2)
}
method m5() { assert fib(10) == 55; } //Remove3:
",
        "m1 m2 m3 m4 fib m5\n" +
        "m3 m1 m2 m4 fib m5\n" +
        "m4 m3 m1 m2 fib m5\n" +
        "m1 m2 m3 m4 fib");
    });
  }


  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethodsWhileTypo() {
    await WithNoopSolver(async () => {
      await TestPriorities(@"
method m1() { assert fib(10) == 55; }
method m2() {
  assert fib(10) == 55;//Next3:  typo//Next5:  assert fib(10) == 55;
}
method m3() {
  assert fib(10) == 55;//Next1:  assert  fib(10) == 55;
} 
method m4() {
  assert fib(10) == 55;//Next2:  assert  fib(10) == 55;
}
function fib(n: nat): nat {
  if (n <= 1) then n else fib(n - 1) + fib(n - 2)
}
method m5() { assert fib(10) == 55; } //Remove4:
",
          "m1 m2 m3 m4 fib m5\n" +
          "m3 m1 m2 m4 fib m5\n" +
          "m4 m3 m1 m2 fib m5\n" +
          "null\n" +
          "m1 m2 m3 m4 fib\n" +
          "m2 m4 m3 m1 fib"
      );
    });
  }

  private Position GetPositionOf(string code, string symbol) {
    var regex = new Regex($"(function|method) (?<name>{symbol})");
    var match = regex.Match(code);
    if (!match.Success) {
      throw new Exception("Could not find '" + symbol + "' in:\n" + code);
    }

    var pos = match.Groups["name"].Index;
    var line = code.Take(pos).Count(c => c == '\n');
    var character = 0;
    while (character <= pos && code[pos - character] != '\n') {
      character++;
    }

    character--;

    return (line, character);
  }

  private IList<Position> GetPositions(string code, IList<string> symbols) {
    return symbols.Select(symbol => GetPositionOf(code, symbol)).ToList();
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
    var initialPositions = GetPositions(code, symbols.First());
    Assert.IsTrue(initialPositions.SequenceEqual(initialOrder),
      $"Expected {string.Join(", ", initialPositions)} but got {string.Join(", ", initialOrder)}");
    foreach (var (change, expectedSymbols) in Enumerable.Zip(changes, symbols.Skip(1))) {
      ApplyChange(ref documentItem, change.changeRange, change.changeValue);
      var expectedPositions = expectedSymbols == null ? null : GetPositions(code, expectedSymbols);
      if (expectedPositions != null) {
        var orderAfterChange = await GetFlattenedPositionOrder(CancellationToken);
        Assert.IsTrue(expectedPositions.SequenceEqual(orderAfterChange),
          $"Expected {string.Join(", ", expectedPositions)} but got {string.Join(", ", orderAfterChange)}." +
          $"\nHistory was: {string.Join("\n", verificationStatusReceiver.History)}");
      }
    }
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