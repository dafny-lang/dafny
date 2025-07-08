﻿using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;

[assembly: CollectionBehavior(DisableTestParallelization = true)]

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.GutterStatus;

[CollectionDefinition("Sequential Collection", DisableParallelization = true)] // These tests are slow and close to hitting their timeout, so we don't run then in parallel with others
public class NonParallelCollection { }

[Collection("Sequential Collection")]
public class CachedLinearVerificationGutterStatusTester : LinearVerificationGutterStatusTester {
  private const int MaxTestExecutionTimeMs = 10000;

  // To add a new test, just call VerifyTrace on a given program,
  // the test will fail and give the correct output that can be use for the test
  // Add '//Replace<n>:' to edit a line multiple times

  [Fact(Timeout = MaxTestExecutionTimeMs)]
  public async Task EnsureCachingDoesNotMakeSquigglyLinesToRemain() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
      options.Set(LanguageServer.VerifySnapshots, 1U);
    });
    await VerifyTrace(@"
 .  S  |  I  $  | :method test() {
 .  S  |  I  $  | :  assert true;
 .  S  |  I  $  | :  //Replace: 
 .  S  |  I  $  | :}", true);
  }

  [Fact]
  public async Task EnsureCachingDoesNotHideErrors() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
      options.Set(LanguageServer.VerifySnapshots, 1U);
    });
    await VerifyTrace(@"
 .  S [ ][I][S][ ]:method test() {
 .  S [O][o][Q][O]:  assert true;
 .  S [=][-][~][=]:  assert false;
 .  S [ ][I][S][ ]:  //Replace: 
 .  S [ ][I][S][ ]:}", false, "ensureCachingDoesNotHideErrors.dfy");
  }

  public CachedLinearVerificationGutterStatusTester(ITestOutputHelper output) : base(output) {
  }
}
