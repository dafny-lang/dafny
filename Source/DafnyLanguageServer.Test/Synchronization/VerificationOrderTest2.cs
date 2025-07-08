﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie.SMTLib;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.GutterStatus;

/// <summary>
/// This class tests whether editing a file results in
/// methods priorities for verification being set automatically.
/// </summary>
public class VerificationOrderTest2 : ClientBasedLanguageServerTest {
  private const int MaxTestExecutionTimeMs = 10000;

  [Fact/*, Timeout(MaxTestExecutionTimeMs * 10)*/]
  public async Task EnsuresPriorityDependsOnEditing() {
    await TestPriorities(@"
method m1() {
  assert false;//Replace2:  assert true;
}
method m2() {
  assert false;//Replace1:  assert true;
}
",
      "m1 m2\n" +
      "m2 m1\n" +
      "m1 m2"
    , "EnsuresPriorityDependsOnEditing.dfy");
  }

  [Fact]
  public async Task EnsuresPriorityDependsOnEditingWhileEditingSameMethod() {
    await TestPriorities(@"
method m1() {
  assert false;//Replace7:  assert  true;//Replace8:  assert false;
}
method m2() {
  assert false;//Replace5:  assert  true;
}
method m3() {
  assert false;//Replace2:  assert  true;//Replace9:  assert false;
}
method m4() {
  assert false;//Replace3:  assert  true;//Replace4:  assert false;
}
method m5() {
  assert false;//Replace1:  assert  true;//Replace6:  assert false;//Replace10:  assert  true;
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
    , "EnsuresPriorityDependsOnEditingWhileEditingSameMethod.dfy");
  }

  [Fact]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethods() {
    await TestPriorities(@"
method m1() { assert false; }
method m2() { assert false; }
method m3() {
  assert false;//Replace1:  assert  true;
} 
method m4() {
  assert false;//Replace2:  assert  true;
}
method m5() { assert false; } //Remove3:
",
      "m1 m2 m3 m4 m5\n" +
      "m3 m1 m2 m4 m5\n" +
      "m4 m3 m1 m2 m5\n" +
      "m4 m3 m1 m2", "EnsuresPriorityWorksEvenIfRemovingMethods.dfy");
  }

  [Fact]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethodsWhileTypo() {
    await TestPriorities(@"
method m1() { assert false; }
method m2() {
  assert false;//Replace3:  typo//Replace5:  assert true;
}
method m3() {
  assert false;//Replace1:  assert  true;
} 
method m4() {
  assert false;//Replace2:  assert  true;
}
method m5() { assert false; } //Remove4:
",
    "m1 m2 m3 m4 m5\n" +
    "m3 m1 m2 m4 m5\n" +
    "m4 m3 m1 m2 m5\n" +
    "null\n" +
    "null\n" +
    "m2 m4 m3 m1"
  , "EnsuresPriorityWorksEvenIfRemovingMethodsWhileTypo.dfy");
  }

  // Requires changes to not change the position of symbols for now, as we are not applying the changes to the local code for now.
  private async Task TestPriorities(string codeAndChanges, string symbolsString, string filePath = null) {
    var semaphoreSlim = new SemaphoreSlim(0);
    await SetUp(options => {
      options.CreateSolver = (_, _) =>
        new UnsatSolver(semaphoreSlim);
      options.Set(BoogieOptionBag.Cores, 1U);
    });
    var symbols = ExtractSymbols(symbolsString);

    var (code, codes, changesList) = LinearVerificationGutterStatusTester.ExtractCodeAndChanges(codeAndChanges.TrimStart());
    var documentItem = CreateTestDocument(code, filePath);
    client.OpenDocument(documentItem);

    var source = new CancellationTokenSource();
    source.CancelAfter(TimeSpan.FromMinutes(5));
    var index = 0;
    // ReSharper disable AccessToModifiedClosure
    async Task CompareWithExpectation(List<string> expectedSymbols) {
      try {
        var orderAfterChange = await GetFlattenedPositionOrder(semaphoreSlim, source.Token);
        var orderAfterChangeSymbols = GetSymbols(code, orderAfterChange).ToList();
        Assert.True(expectedSymbols.SequenceEqual(orderAfterChangeSymbols),
          $"Expected {string.Join(", ", expectedSymbols)} but got {string.Join(", ", orderAfterChangeSymbols)}");
      } catch (OperationCanceledException) {
        WriteVerificationHistory();
        await output.WriteLineAsync($"Operation cancelled for index {index} when expecting: {string.Join(", ", expectedSymbols)}");
        throw;
      }

      index++;
    }

    await CompareWithExpectation(symbols.First());
    foreach (var (changes, expectedSymbols) in changesList.Zip(symbols.Skip(1))) {
      index++;
      ApplyChanges(ref documentItem, changes);
      if (expectedSymbols != null) {
        var migrated = expectedSymbols.Count == 0;
        if (migrated) {
          await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
          continue;
        }

        await CompareWithExpectation(expectedSymbols);
      }
    }
    WriteVerificationHistory();
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
        await output.WriteLineAsync("count: " + count);
        if (foundStatus != null) {
          await output.WriteLineAsync("Found status before timeout: " + string.Join(", ", foundStatus.NamedVerifiables));
        }

        WriteVerificationHistory();
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
        WriteVerificationHistory();
        throw new Exception("semaphore throttling should only allow one newly running per notification.");
      }

      if (newlyReported.Count > 0) {
        semaphore.Release(1);
      }

      yield return newlyReported.ToList();
    } while (!started || foundStatus.NamedVerifiables.Any(v => v.Status < PublishedVerificationStatus.Error));
  }

  public VerificationOrderTest2(ITestOutputHelper output) : base(output) {
  }
}
