using System.Linq;
using System.Threading.Tasks;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Xunit.Abstractions;
using Xunit;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class PluginsAdvancedTest : PluginsTestBase {

  protected override string LibraryName =>
    "PluginsAdvancedTest";

  protected override string[] CommandLineArgument =>
    new[] { $"{LibraryPath},force you" };

  [Fact]
  public async Task EnsureErrorMessageCanBeComplexAndTakeIntoAccountConfiguration() {
    var documentItem = CreateTestDocument(@"
method {:extern} myMethod(i: int) returns (j: int)

method {:test} myMethodWrongName() {
  var result := myMethod(0);
  expect result == 1;
}
");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.Equal(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = resolutionReport.Diagnostics.ToArray();
    Assert.Single(diagnostics);
    Assert.Equal("Please declare a method {:test} named myMethod_test that will call myMethod, you", diagnostics[0].Message);
    Assert.Equal(new Range((1, 17), (1, 25)), diagnostics[0].Range);
    var related = diagnostics[0].RelatedInformation?.GetEnumerator();
    Assert.True(related != null && related.MoveNext());
    Assert.Equal("You might want to just rename this method", related.Current.Message);
    Assert.Equal(new Range((3, 15), (3, 32)), related.Current.Location.Range);
    related.Dispose();
  }

  public PluginsAdvancedTest(ITestOutputHelper output) : base(output) {
  }
}
