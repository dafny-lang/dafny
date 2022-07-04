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
    var m1Position = new Position(0, 7);
    var m2Position = new Position(4, 7);
    await WithNoopSolver(async () => {
      await TestPriorities(@"
method m1() {
  assert 1 == 0;//Next2:  assert 2 == 0;
}

method m2() {
  assert 1 == 0;//Next1:  assert 2 == 0;
}",
        new List<IList<Position>>() {
          new List<Position>() { m1Position, m2Position},
          new List<Position>() { m2Position, m1Position},
          new List<Position>() { m1Position, m2Position},
        });
    });
  }

  [TestMethod]
  public async Task EnsuresPriorityDependsOnEditingWhileEditingSameMethod() {
    var m1Position = new Position(0, 7);
    var m2Position = new Position(3, 7);
    var m3Position = new Position(6, 7);
    var m4Position = new Position(9, 7);
    var m5Position = new Position(12, 7);
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
}",
        new List<IList<Position>>() {
          new List<Position>() { m1Position, m2Position, m3Position, m4Position, m5Position },
          new List<Position>() { m5Position, m1Position, m2Position, m3Position, m4Position },
          new List<Position>() { m3Position, m5Position, m1Position, m2Position, m4Position },
          new List<Position>() { m4Position, m3Position, m5Position, m1Position, m2Position },
          new List<Position>() { m4Position, m3Position, m5Position, m1Position, m2Position },
          new List<Position>() { m2Position, m4Position, m3Position, m5Position, m1Position },
          new List<Position>() { m5Position, m2Position, m4Position, m3Position, m1Position },
          new List<Position>() { m1Position, m5Position, m2Position, m4Position, m3Position },
          new List<Position>() { m1Position, m5Position, m2Position, m4Position, m3Position },
          new List<Position>() { m3Position, m1Position, m5Position, m2Position, m4Position },
          new List<Position>() { m5Position, m3Position, m1Position, m2Position, m4Position },
        });
    });
  }

  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethods() {
    var m1Position = new Position(0, 7);
    var m2Position = new Position(1, 7);
    var m3Position = new Position(2, 7);
    var m4Position = new Position(3, 7);
    var m5Position = new Position(6, 7);
    await WithNoopSolver(async () => {
      await TestPriorities(@"
method m1() { assert true; }
method m2() { assert true; }
method m3() { assert true; } //Remove3:
method m4() {
  assert true;//Next1:  assert  true;
} 
method m5() {
  assert true;//Next2:  assert  true;
}
",
        new List<IList<Position>>() {
          new List<Position>() { m1Position, m2Position, m3Position, m4Position, m5Position },
          new List<Position>() { m4Position, m1Position, m2Position, m3Position, m5Position },
          new List<Position>() { m5Position, m4Position, m1Position, m2Position, m3Position },
          new List<Position>() { },
        });
    });
  }


  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethodsWhileTypo() {
    var m1Position = new Position(0, 7);
    var m2Position = new Position(1, 7);
    var m3Position = new Position(4, 7);
    var m4Position = new Position(7, 7);
    var m5Position = new Position(10, 7);
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
", new List<IList<Position>>() {
          new List<Position>() { m1Position, m2Position, m3Position, m4Position, m5Position },
          new List<Position>() { m3Position, m1Position, m2Position, m4Position, m5Position },
          new List<Position>() { m4Position, m3Position, m1Position, m2Position, m5Position },
          null,
          new List<Position>() { },
          new List<Position>() { m2Position, m4Position, m3Position, m1Position }
          });
    });
  }


  private async Task TestPriorities(string codeAndChanges, IList<IList<Position>> positions) {
    await SetUp(new Dictionary<string, string>() {
    { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", "1" },
    });

    var (code, changes) = ExtractCodeAndChanges(codeAndChanges.TrimStart());
    var documentItem = CreateTestDocument(code);
    client.OpenDocument(documentItem);

    var initialOrder = await GetFlattenedPositionOrder(CancellationToken);
    Assert.IsTrue(positions.First().SequenceEqual(initialOrder),
      $"Expected {string.Join(", ", positions.First())} but got {string.Join(", ", initialOrder)}");
    foreach (var (change, expectedPositions) in changes.Zip(positions.Skip(1))) {
      ApplyChange(ref documentItem, change.changeRange, change.changeValue);
      if (expectedPositions != null) {
        var orderAfterChange = await GetFlattenedPositionOrder(CancellationToken);
        Assert.IsTrue(expectedPositions.SequenceEqual(orderAfterChange),
          $"Expected {string.Join(", ", expectedPositions)} but got {string.Join(", ", orderAfterChange)}");
      }
    }
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