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
    : s  |  |  |  I  I  |  | :predicate Ok() {
    : s  |  |  |  I  I  |  | :  true
    : s  |  |  |  I  I  |  | :}
    :    |  |  |  I  I  |  | :
    : s  S [S][ ][I][I][S] | :method Test(x: bool) returns (i: int)
    : s  S [=][=][-][-][~] | :   ensures i == 2
    : s  S [S][ ][I][I][S] | :{
    : s  S [S][ ][I][I][S] | :  if x {
    : s  S [S][ ][I][I][S] | :    i := 2;
    : s  S [=][=][-][-][~] | :  } else {
    : s  S [S][ ]/!\[I][S] | :    i := 1; //Next1:   i := /; //Next2:    i := 2;
    : s  S [S][ ][I][I][S] | :  }
    : s  S [S][ ][I][I][S] | :}
    :    |  |  |  I  I  |  | :    
    : s  |  |  |  I  I  |  | :predicate OkBis() {
    : s  |  |  |  I  I  |  | :  false
    : s  |  |  |  I  I  |  | :}");
  }
  [TestMethod]
  public async Task EnsuresItWorksForSubsetTypes() {
    await VerifyTrace(@"
:    |  | :
:    |  | :ghost const maxId := 200;
:    |  | :
: s  |  | :predicate isIssueIdValid(issueId: int) {
: s  |  | :  101 <= issueId < maxId
: s  |  | :}
:    |  | :
: s  S  | :type IssueId = i : int | isIssueIdValid(i)
: s  S  | :  witness 101 //Next1:   witness 99 //Next2:   witness 101 ");
  }
}