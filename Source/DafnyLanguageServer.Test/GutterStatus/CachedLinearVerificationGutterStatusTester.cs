using System.Threading.Tasks;
using Xunit.Abstractions;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

[CollectionDefinition("Sequential Collection", DisableParallelization = true)] // These tests are slow and close to hitting their timeout, so we don't run then in parallel with others
public class NonParallelCollection { }

[Collection("Sequential Collection")]
public class CachedLinearVerificationGutterStatusTester : LinearVerificationGutterStatusTester {
  private const int MaxTestExecutionTimeMs = 10000;

  // To add a new test, just call VerifyTrace on a given program,
  // the test will fail and give the correct output that can be use for the test
  // Add '//Next<n>:' to edit a line multiple times

  [Fact(Timeout = MaxTestExecutionTimeMs)]
  public async Task EnsureCachingDoesNotMakeSquigglyLinesToRemain() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
      options.Set(ServerCommand.VerifySnapshots, 1U);
    });
    await VerifyTrace(@"
 .  S  S  |  I  $  | :method test() {
 .  S  |  |  I  $  | :  assert true;
 .  S  S  |  I  $  | :  //Next: 
 .  S  S  |  I  $  | :}");
  }

  [Fact(Timeout = MaxTestExecutionTimeMs)]
  public async Task EnsureCachingDoesNotHideErrors() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
      options.Set(ServerCommand.VerifySnapshots, 1U);
    });
    await VerifyTrace(@"
 .  S [S][ ][I][S][S][ ]:method test() {
 .  S [O][O][o][Q][O][O]:  assert true;
 .  S [=][=][-][~][=][=]:  assert false;
 .  S [S][ ][I][S][S][ ]:  //Next: 
 .  S [S][ ][I][S][S][ ]:}");
  }

  public CachedLinearVerificationGutterStatusTester(ITestOutputHelper output) : base(output)
  {
  }
}
