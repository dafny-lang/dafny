using System;
using System.Collections.Generic;
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
    var dafnyOptions = DafnyOptions.CreateUsingOldParser(TextWriter.Null, TextReader.Null);
    var compilationManager = new Compilation(new Mock<ILogger<Compilation>>().Object,
      new Mock<IFileSystem>().Object,
      new Mock<ITextDocumentLoader>().Object,
      new Mock<IProgramVerifier>().Object,
      null!, new CompilationInput(dafnyOptions, 0,
        new DafnyProject(null, new Uri(Directory.GetCurrentDirectory()), null, new HashSet<string>())));
    compilationManager.CancelPendingUpdates();
    await Assert.ThrowsAsync<TaskCanceledException>(() => compilationManager.ParsedProgram);
  }
}