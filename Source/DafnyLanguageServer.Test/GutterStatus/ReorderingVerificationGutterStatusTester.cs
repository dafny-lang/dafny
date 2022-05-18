using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Various;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using Microsoft.Extensions.DependencyInjection;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

/// <summary>
/// This class tests whether editing a file results in
/// methods priorities for verification being set automatically.
/// </summary>
[TestClass]
public class ReorderingVerificationGutterStatusTester : LinearVerificationGutterStatusTester {
  private ListeningTextDocumentLoader textDocumentLoader;
  private const int MaxTestExecutionTimeMs = 10000;

  [TestInitialize]
  public override async Task SetUp() {
    DafnyOptions.Install(DafnyOptions.Create("-proverOpt:SOLVER=noop"));
    verificationStatusGutterReceiver = new();
    client = await InitializeClient(options =>
        options
          .AddHandler(DafnyRequestNames.VerificationStatusGutter,
            NotificationHandler.For<VerificationStatusGutter>(verificationStatusGutterReceiver.NotificationReceived))
      , serverOptions => {
        serverOptions.Services.AddSingleton<ITextDocumentLoader>(serviceProvider => {
          textDocumentLoader = new ListeningTextDocumentLoader(
            serviceProvider.GetRequiredService<ILoggerFactory>(), serviceProvider.GetRequiredService<IDafnyParser>(),
            serviceProvider.GetRequiredService<ISymbolResolver>(),
            serviceProvider.GetRequiredService<IProgramVerifier>(),
            serviceProvider.GetRequiredService<ISymbolTableFactory>(),
            serviceProvider.GetRequiredService<IGhostStateDiagnosticCollector>(),
            serviceProvider.GetRequiredService<ICompilationStatusNotificationPublisher>(),
            serviceProvider.GetRequiredService<IDiagnosticPublisher>(),
            serviceProvider.GetRequiredService<IOptions<VerifierOptions>>().Value
          );
          return textDocumentLoader;
        });
      });
  }

  [TestMethod/*, Timeout(MaxTestExecutionTimeMs * 10)*/]
  public async Task EnsuresPriorityDependsOnEditing() {
    await TestPriorities(@"
method m1() {
  assert 1 == 0;//Next2:  assert 2 == 0;
}

method m2() {
  assert 1 == 0;//Next1:  assert 2 == 0;
}",
      expectedPriorities:
      " 1, 1 " +
      " 1,10 " +
      "10, 9");
  }

  [TestMethod]
  public async Task EnsuresPriorityDependsOnEditingWhileEditingSameMethod() {
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
}", expectedPriorities:
      " 1, 1, 1, 1, 1 " +
      " 1, 1, 1, 1,10 " +
      " 1, 1,10, 1, 9 " +
      " 1, 1, 9,10, 8 " +
      " 1, 1, 9,10, 8 " +
      " 1,10, 8, 9, 7 " +
      " 1, 9, 7, 8,10 " +
      "10, 8, 6, 7, 9 " +
      "10, 8, 6, 7, 9 " +
      " 9, 7,10, 6, 8 " +
      " 8, 7, 9, 6,10");
  }

  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethods() {
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
", expectedPriorities:
      " 1, 1, 1, 1, 1 " +
      " 1, 1, 1,10, 1 " +
      " 1, 1, 1, 9,10 " +
      " 1, 1, 9,10");
  }


  [TestMethod]
  public async Task EnsuresPriorityWorksEvenIfRemovingMethodsWhileTypo() {
    await TestPriorities(@"
method m1() { assert true; }
method m2() {
  assert true;//Next3:  typo//Next5:  assert true;
}
method m3() { assert true; } //Remove4:
method m4() {
  assert true;//Next1:  assert  true;
} 
method m5() {
  assert true;//Next2:  assert  true;
}
", expectedPriorities:
      " 1, 1, 1, 1, 1 " +
      " 1, 1, 1,10, 1 " +
      " 1, 1, 1, 9,10 " +// No priorities set for the two edits when there is a parse error.
      " 1,10, 8, 9");
  }

  private async Task TestPriorities(string code, string expectedPriorities) {
    textDocumentLoader.LinearPriorities = new List<List<int>>();
    await VerifyTrace(code, testTrace: false);
    var priorities = string.Join(" ", textDocumentLoader.LinearPriorities.Select(priorities =>
      string.Join(",", priorities.Select(priority => priority.ToString().PadLeft(2)))));
    Assert.AreEqual(expectedPriorities, priorities);
  }

  [TestCleanup]
  public void Cleanup() {
    DafnyOptions.Install(DafnyOptions.Create());
  }
}