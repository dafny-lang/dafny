using System;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Moq;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Unit; 

public class CompilationManagerTest {
  [Fact]
  public async Task CancelUnstartedCompilationLeadsToCancelledTasks() {
    var dafnyOptions = DafnyOptions.Create(TextWriter.Null, TextReader.Null);
    var compilationManager = new CompilationManager(new Mock<ILogger<CompilationManager>>().Object,
      new Mock<ITextDocumentLoader>().Object,
      new Mock<INotificationPublisher>().Object,
      new Mock<IProgramVerifier>().Object,
      new Mock<ICompilationStatusNotificationPublisher>().Object,
      new Mock<IVerificationProgressReporter>().Object,
      dafnyOptions,
      null, new Compilation(0, new DafnyProject(), new Uri[] { }), null);
    compilationManager.CancelPendingUpdates();
    await Assert.ThrowsAsync<TaskCanceledException>(() => compilationManager.ResolvedCompilation);
  }
}