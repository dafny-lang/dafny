using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

[TestClass]
public class SimpleLinearVerificationDiagnosticTester : LinearVerificationDiagnosticTester {
  private const int MaxTestExecutionTimeMs = 10000;

  // To add a new test, just call VerifyTrace on a given program,
  // the test will fail and give the correct output that can be use for the test
  // Add '//Next<n>:' to edit a line multiple times

  [TestMethod, Timeout(MaxTestExecutionTimeMs)]
  public async Task EnsureVerificationDiagnosticsAreWorking() {
    await VerifyTrace(@"
    : .  |  |  |  I  I  |  | :predicate Ok() {
    : .  |  |  |  I  I  |  | :  true
    : .  |  |  |  I  I  |  | :}
    :    |  |  |  I  I  |  | :
    : .  S [S][ ][I][I][S] | :method Test(x: bool) returns (i: int)
    : .  S [=][=][-][-][~] | :   ensures i == 2
    : .  S [S][ ][I][I][S] | :{
    : .  S [S][ ][I][I][S] | :  if x {
    : .  S [S][ ][I][I][S] | :    i := 2;
    : .  S [=][=][-][-][~] | :  } else {
    : .  S [S][ ]/!\[I][S] | :    i := 1; //Next1:   i := /; //Next2:    i := 2;
    : .  S [S][ ][I][I][S] | :  }
    : .  S [S][ ][I][I][S] | :}
    :    |  |  |  I  I  |  | :    
    : .  |  |  |  I  I  |  | :predicate OkBis() {
    : .  |  |  |  I  I  |  | :  false
    : .  |  |  |  I  I  |  | :}");
  }
  [TestMethod]
  public async Task EnsuresItWorksForSubsetTypes() {
    await VerifyTrace(@"
    |  |  I  I  |  | :
 .  |  |  I  I  |  | :ghost const maxId := 200;
    |  |  I  I  |  | :
 .  |  |  I  I  |  | :predicate isIssueIdValid(issueId: int) {
 .  |  |  I  I  | [=]:  101 <= issueId < maxId
 .  |  |  I  I  |  | :}
    |  |  I  I  |  | :
 .  S  |  I  .  S [=]:type IssueId = i : int | isIssueIdValid(i)
 .  S  |  I  .  S [=]:  witness 101 //Next1:   witness 99 //Next2:   witness 101 ");
  }

  [TestMethod]
  public async Task EnsureItWorksForPostconditionsRelatedOutside() {
    await VerifyTrace(@"
predicate F(i: int) {
  false // Should not be highlighted in gutter.
}

method H()
  ensures F(1)
{
}".Substring(1));
  }

  [TestMethod]
  public async Task EnsuresEditingChangesPriority() {
    await VerifyTrace(@"
                |  |  I  I  $  |  |  |  I  $  $             :
 .  .  S  S  S  |  |  I  I  $  |  |  |  I  $  $ [S][ ][ ][ ]:method {:priority 5} A1() {
 .  .  S  S  |  |  |  I  I  $  |  |  |  I  $  $ [=][=][=][=]:  assert 1 == 1; //Next2:  assert 1 == 2;
 .  .  S  S  S  |  |  I  I  $  |  |  |  I  $  $ [S][ ][ ][ ]:}
 .  S  S  S  S  S  |  I  $  $  $ [S][ ][I][I][S][S][S][S][ ]:method {:priority 1} A2() {
 .  S  S  |  |  |  |  I  $  $  $ [=][=][-][-][~][~][~][=][=]:  assert 1 == 1; //Next1:  assert 1 == 2;
 .  S  S  S  S  S  |  I  $  $  $ [S][ ][I][I][S][S][S][S][ ]:}".Substring(1));
  }
}