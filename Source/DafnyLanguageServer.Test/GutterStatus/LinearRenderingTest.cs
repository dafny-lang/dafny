using System;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

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

  [Fact]
  public void EnsureRenderingIsCoherent() {
    foreach (GutterVerificationStatus verificationStatus in Enum.GetValues(typeof(GutterVerificationStatus))) {
      foreach (CurrentStatus currentStatus in Enum.GetValues(typeof(CurrentStatus))) {
        var isSingleLine = true; do {
          var contextHasError = true; do {
            var contextIsPending = true; do {
              Assert.Equal(
                RenderLineVerificationStatusOriginal(isSingleLine, contextHasError, contextIsPending, currentStatus, verificationStatus),
                VerificationTree.RenderLineVerificationStatus(isSingleLine, contextHasError, contextIsPending, currentStatus, verificationStatus)
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
