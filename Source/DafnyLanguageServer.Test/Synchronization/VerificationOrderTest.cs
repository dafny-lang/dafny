using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

[Collection("Sequential Collection")]
public class VerificationOrderTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task MigrationOfRecentlyRelatedChanges() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
      options.Set(ProjectManager.Verification, VerifyOnMode.ChangeProject);
    });

    var sourceA = @"
method Foo() {
  assert false;
}
".TrimStart();

    var directory = Path.GetRandomFileName();
    var firstFile = await CreateOpenAndWaitForResolve(sourceA, Path.Combine(directory, "firstFile.dfy"));

    await WaitUntilCompletedForUris(1, CancellationToken);

    ApplyChange(ref firstFile, new Range(3, 0, 3, 0), "method GetsPriority() { assert false; }\n");
    var history1 = await WaitUntilCompletedForUris(1, CancellationToken);
    AssertExpectedOrderForFirstFile(history1, new Range(3, 7, 3, 19));
    ApplyChange(ref firstFile, new Range(0, 0, 0, 0), "//comment before assert false\n");

    var history2 = await WaitUntilCompletedForUris(1, CancellationToken);
    AssertExpectedOrderForFirstFile(history2, new Range(4, 7, 4, 19));

    void AssertExpectedOrderForFirstFile(IList<FileVerificationStatus> history, Range expectedRange) {
      var firstErrorStatus = history.First(h =>
        h.Uri == firstFile.Uri && h.NamedVerifiables.Any(v => v.Status == PublishedVerificationStatus.Error));
      var errorRange = firstErrorStatus.NamedVerifiables.First(v => v.Status == PublishedVerificationStatus.Error);
      Assert.Equal(expectedRange, errorRange.NameRange);
      Assert.Contains(firstErrorStatus.NamedVerifiables, v => v.Status != PublishedVerificationStatus.Error);
    }
  }

  [Fact]
  public async Task VerificationPriorityBasedOnChangesWorksWithMultipleFiles() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
      options.Set(ProjectManager.Verification, VerifyOnMode.ChangeProject);
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
    await CreateOpenAndWaitForResolve("", Path.Combine(directory, DafnyProject.FileName));
    var firstFile = await CreateOpenAndWaitForResolve(sourceA, Path.Combine(directory, "firstFile.dfy"));
    var secondFile = await CreateOpenAndWaitForResolve(sourceB, Path.Combine(directory, "secondFile.dfy"));

    await WaitUntilCompletedForUris(2, CancellationToken);

    ApplyChange(ref firstFile, new Range(3, 0, 3, 0), "method GetsPriority() { assert false; }\n");
    var history2 = await WaitUntilCompletedForUris(2, CancellationToken);
    AssertExpectedOrderForFirstFile(history2);
    /*
     * This change is chosen so that without a Uri check, it would incorrectly migrate the previously made change (in a different file!)
     * so it wouldn't map to a GetsPriority any more and change the verification order
     */
    ApplyChange(ref secondFile, new Range(1, 0, 1, 0), "  //comment before assert false\n");

    var history3 = await WaitUntilCompletedForUris(2, CancellationToken);

    AssertExpectedOrderForFirstFile(history3);
    Assert.Equal(firstFile.Uri.ToUri(), history3[^1].Uri);

    void AssertExpectedOrderForFirstFile(IList<FileVerificationStatus> history) {
      var firstErrorStatus = history.First(h =>
        h.Uri == firstFile.Uri && h.NamedVerifiables.Any(v => v.Status == PublishedVerificationStatus.Error));
      var errorRange = firstErrorStatus.NamedVerifiables.First(v => v.Status == PublishedVerificationStatus.Error);
      Assert.Equal(new Range(3, 7, 3, 19), errorRange.NameRange);
      Assert.Contains(firstErrorStatus.NamedVerifiables, v => v.Status != PublishedVerificationStatus.Error);
    }
  }

  public VerificationOrderTest(ITestOutputHelper output) : base(output) {
  }
}