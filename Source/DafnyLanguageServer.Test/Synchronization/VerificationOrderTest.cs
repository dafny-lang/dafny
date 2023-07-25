using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization; 

public class VerificationOrderTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task VerificationPriorityBasedOnChangesWorksWithMultipleFiles() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
      options.Set(ServerCommand.ProjectMode, true);
    });

    var sourceA = @"
method Foo() {
  assert false;
}
".TrimStart();

    var sourceB = @"
method Bar() {
  assert false;
}
".TrimStart();

    var directory = Path.GetRandomFileName();
    var projectFile = await CreateAndOpenTestDocument("", Path.Combine(directory, DafnyProject.FileName));
    var firstFile = await CreateAndOpenTestDocument(sourceA, Path.Combine(directory, "firstFile.dfy"));
    var secondFile = await CreateAndOpenTestDocument(sourceB, Path.Combine(directory, "secondFile.dfy"));

    var history0 = await WaitUntilCompletedForUris(2, CancellationToken);

    ApplyChange(ref secondFile, new Range(1, 0, 1, 0), "  //comment before assert false\n");

    var history1 = await WaitUntilCompletedForUris(2, CancellationToken);
    Assert.Equal(firstFile.Uri.ToUri(), history1[^1].Uri);
    ApplyChange(ref firstFile, new Range(1, 0, 1, 0), "  //comment before assert false\n");

    var history2 = await WaitUntilCompletedForUris(2, CancellationToken);
    Assert.Equal(secondFile.Uri.ToUri(), history2[^1].Uri);
  }

  public VerificationOrderTest(ITestOutputHelper output) : base(output) {
  }
}