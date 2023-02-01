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
public class LinearRenderingTest {
  public static LineVerificationStatus RenderLineVerificationStatusOriginal(
      bool isSingleLine, bool contextHasErrors, bool contextIsPending,
      CurrentStatus currentStatus, GutterVerificationStatus verificationStatus) {
    return verificationStatus switch {
      GutterVerificationStatus.Nothing =>
        currentStatus switch {
          CurrentStatus.Current => LineVerificationStatus.Nothing,
          CurrentStatus.Obsolete => LineVerificationStatus.Scheduled,
          CurrentStatus.Verifying => LineVerificationStatus.Verifying,
          _ => throw new ArgumentOutOfRangeException()
        },
      // let's be careful to no display "Verified" for a range if the context does not have errors and is pending
      // because there might be other errors on the same range.
      GutterVerificationStatus.Verified => currentStatus switch {
        CurrentStatus.Current => contextHasErrors
          ? isSingleLine // Sub-implementations that are verified do not count
            ? LineVerificationStatus.AssertionVerifiedInErrorContext
            : LineVerificationStatus.ErrorContext
          : contextIsPending && !isSingleLine
            ? LineVerificationStatus.Nothing
            : LineVerificationStatus.Verified,
        CurrentStatus.Obsolete => contextHasErrors
          ? isSingleLine
            ? LineVerificationStatus.AssertionVerifiedInErrorContextObsolete
            : LineVerificationStatus.ErrorContextObsolete
          : contextIsPending && !isSingleLine
            ? LineVerificationStatus.Scheduled
            : LineVerificationStatus.VerifiedObsolete,
        CurrentStatus.Verifying => contextHasErrors
          ? isSingleLine
            ? LineVerificationStatus.AssertionVerifiedInErrorContextVerifying
            : LineVerificationStatus.ErrorContextVerifying
          : contextIsPending && !isSingleLine ?
            LineVerificationStatus.Verifying
            : LineVerificationStatus.VerifiedVerifying,
        _ => throw new ArgumentOutOfRangeException()
      },
      // If a node is marked with VerifiedWithAssumption
      GutterVerificationStatus.VerifiedWithAssumption => currentStatus switch {
        CurrentStatus.Current => contextHasErrors && isSingleLine
                                 || !contextHasErrors && contextIsPending && !isSingleLine
            ? LineVerificationStatus.Nothing
            : LineVerificationStatus.VerifiedWithAssumption,
        CurrentStatus.Obsolete => contextHasErrors && isSingleLine
         || !contextHasErrors && contextIsPending && !isSingleLine
          ? LineVerificationStatus.Scheduled
            : LineVerificationStatus.VerifiedWithAssumptionObsolete,
        CurrentStatus.Verifying => contextHasErrors && isSingleLine ||
            !contextHasErrors && (contextIsPending && !isSingleLine)
            ? LineVerificationStatus.Verifying
            : LineVerificationStatus.VerifiedWithAssumptionVerifying,
        _ => throw new ArgumentOutOfRangeException()
      },
      // We don't display inconclusive on the gutter (user should focus on errors),
      // We display an error range instead
      GutterVerificationStatus.Inconclusive => currentStatus switch {
        CurrentStatus.Current => LineVerificationStatus.ErrorContext,
        CurrentStatus.Obsolete => LineVerificationStatus.ErrorContextObsolete,
        CurrentStatus.Verifying => LineVerificationStatus.ErrorContextVerifying,
        _ => throw new ArgumentOutOfRangeException()
      },
      GutterVerificationStatus.Error => currentStatus switch {
        CurrentStatus.Current => isSingleLine ? LineVerificationStatus.AssertionFailed : LineVerificationStatus.ErrorContext,
        CurrentStatus.Obsolete => isSingleLine
          ? LineVerificationStatus.AssertionFailedObsolete
          : LineVerificationStatus.ErrorContextObsolete,
        CurrentStatus.Verifying => isSingleLine
          ? LineVerificationStatus.AssertionFailedVerifying
          : LineVerificationStatus.ErrorContextVerifying,
        _ => throw new ArgumentOutOfRangeException()
      },
      _ => throw new ArgumentOutOfRangeException()
    };
  }

  [TestMethod]
  public void EnsureRenderingIsCoherent() {
    foreach (GutterVerificationStatus verificationStatus in Enum.GetValues(typeof(GutterVerificationStatus))) {
      foreach (CurrentStatus currentStatus in Enum.GetValues(typeof(CurrentStatus))) {
        var isSingleLine = true; do {
          var contextHasError = true; do {
            var contextIsPending = true; do {
              Assert.AreEqual(
                RenderLineVerificationStatusOriginal(isSingleLine, contextHasError, contextIsPending, currentStatus, verificationStatus),
                VerificationTree.RenderLineVerificationStatus(isSingleLine, contextHasError, contextIsPending, currentStatus, verificationStatus)
                , "verificationStatus={0}, currentStatus={1} isSingleLine={2}, contextHasError={3}, contextIsPending={4}",
                  verificationStatus, currentStatus, isSingleLine, contextHasError, contextIsPending
                );
              contextIsPending = !contextIsPending;
            } while (!contextIsPending);
            contextHasError = !contextHasError;
          } while (!contextHasError);
          isSingleLine = !isSingleLine;
        } while (!isSingleLine);
      }
    }
  }
}