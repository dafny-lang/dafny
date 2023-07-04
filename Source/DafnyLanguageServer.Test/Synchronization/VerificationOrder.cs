using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization; 

public class VerificationOrder : ClientBasedLanguageServerTest {

  [Fact]
  public async Task VerificationPriorityBasedOnChangesWorksWithMultipleFiles() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
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
    var projectFile = CreateTestDocument("", Path.Combine(directory, "dfyconfig.toml"));
    await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);
    var firstFile = CreateTestDocument(sourceA, Path.Combine(directory, "firstFile.dfy"));
    await client.OpenDocumentAndWaitAsync(firstFile, CancellationToken);
    var secondFile = CreateTestDocument(sourceB, Path.Combine(directory, "secondFile.dfy"));
    await client.OpenDocumentAndWaitAsync(secondFile, CancellationToken);

    var history0 = await WaitUntilCompletedForUris(2, CancellationToken);

    ApplyChange(ref secondFile, new Range(1, 0, 1, 0), "  //comment before assert false\n");

    var history1 = await WaitUntilCompletedForUris(2, CancellationToken);
    Assert.Equal(firstFile.Uri.ToUri(), history1[^1].Uri);
    ApplyChange(ref firstFile, new Range(1, 0, 1, 0), "  //comment before assert false\n");

    var history2 = await WaitUntilCompletedForUris(2, CancellationToken);
    Assert.Equal(secondFile.Uri.ToUri(), history2[^1].Uri);
  }

  public VerificationOrder(ITestOutputHelper output) : base(output)
  {
  }
}