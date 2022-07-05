using System;
using System.Collections.Generic;
using System.Linq;
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
  assert 1 == 0;//Next2:  assert 2 == 0;
}

method m2() {
  assert 1 == 0;//Next1:  assert 2 == 0;
}",
        "m1 m2\n" +
        "m2 m1\n" +
        "m1 m2"
        );
    });
  }

  [TestMethod]
  public async Task EnsuresPriorityDependsOnEditingWhileEditingSameMethod() {
    await WithNoopSolver(async () => {
      await TestPriorities(@"
method m1() {
  assert true;//Next7:  assert  true;//Next8:  assert true;
}
method m2() {
  assert true;//Next5:  assert  true;
}
method m3() {
  assert true;//Next2:  assert  true;//Next9:  assert true;
}
method m4() {
  assert true;//Next3:  assert  true;//Next4:  assert true;
}
method m5() {
  assert true;//Next1:  assert  true;//Next6:  assert true;//Next10:  assert  true;
}", "m1 m2 m3 m4 m5\n" +
          "m5 m1 m2 m3 m4\n" +
          "m3 m5 m1 m2 m4\n" +
          "m4 m3 m5 m1 m2\n" +
          "m4 m3 m5 m1 m2\n" +
          "m2 m4 m3 m5 m1\n" +
          "m5 m2 m4 m3 m1\n" +
          "m1 m5 m2 m4 m3\n" +
          "m1 m5 m2 m4 m3\n" +
          "m3 m1 m5 m2 m4\n" +
          "m5 m3 m1 m2 m4"
        );
    });
  }

  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethods() {
    await WithNoopSolver(async () => {
      await TestPriorities(@"
method m1() { assert true; }
method m2() { assert true; }
method m3() {
  assert true;//Next1:  assert  true;
} 
method m4() {
  assert true;//Next2:  assert  true;
}
method m5() { assert true; } //Remove3:
",
        "m1 m2 m3 m4 m5\n" +
        "m3 m1 m2 m4 m5\n" +
        "m4 m3 m1 m2 m5\n" +
        "m1 m2 m3 m4");
    });
  }


  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethodsWhileTypo() {
    await WithNoopSolver(async () => {
      await TestPriorities(@"
method m1() { assert true; }
method m2() {
  assert true;//Next3:  typo//Next5:  assert true;
}
method m3() {
  assert true;//Next1:  assert  true;
} 
method m4() {
  assert true;//Next2:  assert  true;
}
method m5() { assert true; } //Remove4:
",
          "m1 m2 m3 m4 m5\n" +
          "m3 m1 m2 m4 m5\n" +
          "m4 m3 m1 m2 m5\n" +
          "null\n" +
          "m1 m2 m3 m4\n" +
          "m2 m4 m3 m1"
      );
    });
  }

  private Position GetPositionOf(string code, string symbol) {
    var pos = code.IndexOf(symbol, StringComparison.Ordinal);
    if (pos == -1) {
      throw new Exception("Could not find '" + symbol + "' in:\n" + code);
    }
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