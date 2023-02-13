using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie.SMTLib;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

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
  assert false;//Next2:  assert true;
}
method m2() {
  assert false;//Next1:  assert true;
}
",
      "m1 m2\n" +
      "m2 m1\n" +
      "m1 m2"
    );
  }

  [TestMethod]
  public async Task EnsuresPriorityDependsOnEditingWhileEditingSameMethod() {
    await TestPriorities(@"
method m1() {
  assert false;//Next7:  assert  true;//Next8:  assert false;
}
method m2() {
  assert false;//Next5:  assert  true;
}
method m3() {
  assert false;//Next2:  assert  true;//Next9:  assert false;
}
method m4() {
  assert false;//Next3:  assert  true;//Next4:  assert false;
}
method m5() {
  assert false;//Next1:  assert  true;//Next6:  assert false;//Next10:  assert  true;
}
", "m1 m2 m3 m4 m5\n" +
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
  }

  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethods() {
    await TestPriorities(@"
method m1() { assert false; }
method m2() { assert false; }
method m3() {
  assert false;//Next1:  assert  true;
} 
method m4() {
  assert false;//Next2:  assert  true;
}
method m5() { assert false; } //Remove3:
",
      "m1 m2 m3 m4 m5\n" +
      "m3 m1 m2 m4 m5\n" +
      "m4 m3 m1 m2 m5\n" +
      "m4 m3 m1 m2");
  }

  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethodsWhileTypo() {
    await TestPriorities(@"
method m1() { assert false; }
method m2() {
  assert false;//Next3:  typo//Next5:  assert true;
}
method m3() {
  assert false;//Next1:  assert  true;
} 
method m4() {
  assert false;//Next2:  assert  true;
}
method m5() { assert false; } //Remove4:
",
    "m1 m2 m3 m4 m5\n" +
    "m3 m1 m2 m4 m5\n" +
    "m4 m3 m1 m2 m5\n" +
    "null\n" +
    "null\n" +
    "m2 m4 m3 m1"
  );
  }

  // Requires changes to not change the position of symbols for now, as we are not applying the changes to the local code for now.
  private async Task TestPriorities(string codeAndChanges, string symbolsString) {
    var symbols = ExtractSymbols(symbolsString);
    var semaphoreSlim = new SemaphoreSlim(0);
    var original = DafnyOptions.O.CreateSolver;
    DafnyOptions.O.CreateSolver = (_, _) =>
      new UnsatSolver(semaphoreSlim);
    await SetUp(options => options.Set(BoogieOptionBag.Cores, 1U));

    var (code, changes) = ExtractCodeAndChanges(codeAndChanges.TrimStart());
    var documentItem = CreateTestDocument(code);
    client.OpenDocument(documentItem);

    var index = 0;
    // ReSharper disable AccessToModifiedClosure
    async Task CompareWithExpectation(List<string> expectedSymbols) {
      try {
        var orderAfterChange = await GetFlattenedPositionOrder(semaphoreSlim, CancellationToken);
        var orderAfterChangeSymbols = GetSymbols(code, orderAfterChange).ToList();
        Assert.IsTrue(expectedSymbols.SequenceEqual(orderAfterChangeSymbols),
          $"Expected {string.Join(", ", expectedSymbols)} but got {string.Join(", ", orderAfterChangeSymbols)}." +
          $"\nOld to new history was: {verificationStatusReceiver.History.Stringify()}");
      } catch (OperationCanceledException) {
        Console.WriteLine($"Operation cancelled for index {index} when expecting: {string.Join(", ", expectedSymbols)}");
        throw;
      }

      index++;
    }

    await CompareWithExpectation(symbols.First());
    foreach (var (change, expectedSymbols) in changes.Zip(symbols.Skip(1))) {
      index++;
      ApplyChange(ref documentItem, change.changeRange, change.changeValue);
      if (expectedSymbols != null) {
        var migrated = expectedSymbols.Count == 0;
        if (migrated) {
          await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
          continue;
        }

        await CompareWithExpectation(expectedSymbols);
      }
    }

    DafnyOptions.O.CreateSolver = original;
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
      .Select(array => array switch {
        "null" => null,
        "migrated" => new List<string> {
          Capacity = 0
        },
        _ => array.Split(" ").ToList()
      }).ToList();
  }

  private async Task<List<Position>> GetFlattenedPositionOrder(SemaphoreSlim semaphore, CancellationToken cancellationToken) {
    return (await GetRunningOrder(semaphore, cancellationToken).ToListAsync(cancellationToken)).
      SelectMany(r => r).
      Select(r => r.Start).ToList();
  }

  public async IAsyncEnumerable<List<Range>> GetRunningOrder(SemaphoreSlim semaphore, [EnumeratorCancellation] CancellationToken cancellationToken) {
    var alreadyReported = new HashSet<Range>();
    FileVerificationStatus foundStatus = null;
    int count = 0;
    bool started = false;
    do {
      try {
        foundStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
        count++;

      } catch (OperationCanceledException) {
        Console.WriteLine("count: " + count);
        if (foundStatus != null) {
          Console.WriteLine("Found status before timeout: " + string.Join(", ", foundStatus.NamedVerifiables));
        }
        Console.WriteLine($"\nOld to new history was: {verificationStatusReceiver.History.Stringify()}");
        throw;
      }

      if (!started) {
        if (foundStatus.NamedVerifiables.Any(v => v.Status == PublishedVerificationStatus.Running)) {
          started = true;
        } else {
          continue;
        }
      }
      var newlyDone = foundStatus.NamedVerifiables.Where(v => v.Status >= PublishedVerificationStatus.Error)
        .Select(v => v.NameRange).Where(r => alreadyReported.Add(r));

      var newlyRunning = foundStatus.NamedVerifiables.Where(v => v.Status == PublishedVerificationStatus.Running)
        .Select(v => v.NameRange).Where(r => alreadyReported.Add(r));

      var newlyReported = newlyDone.Concat(newlyRunning).ToList();
      if (newlyReported.Count > 1) {
        throw new Exception("semaphore throttling should only allow one newly running per notification.");
      }

      if (newlyReported.Count > 0) {
        semaphore.Release(1);
      }

      yield return newlyReported.ToList();
    } while (!started || foundStatus.NamedVerifiables.Any(v => v.Status < PublishedVerificationStatus.Error));
  }

  [TestCleanup]
  public void Cleanup() {
    DafnyOptions.Install(DafnyOptions.Create());
  }
}
