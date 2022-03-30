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
      CurrentStatus currentStatus, VerificationStatus verificationStatus) {
    return verificationStatus switch {
      VerificationStatus.Unknown =>
        currentStatus switch {
          CurrentStatus.Current => LineVerificationStatus.Unknown,
          CurrentStatus.Obsolete => LineVerificationStatus.Scheduled,
          CurrentStatus.Verifying => LineVerificationStatus.Verifying,
          _ => throw new ArgumentOutOfRangeException()
        },
      // let's be careful to no display "Verified" for a range if the context does not have errors and is pending
      // because there might be other errors on the same range.
      VerificationStatus.Verified => currentStatus switch {
        CurrentStatus.Current => contextHasErrors
          ? isSingleLine // Sub-implementations that are verified do not count
            ? LineVerificationStatus.ErrorRangeAssertionVerified
            : LineVerificationStatus.ErrorRange
          : contextIsPending && !isSingleLine
            ? LineVerificationStatus.Unknown
            : LineVerificationStatus.Verified,
        CurrentStatus.Obsolete => contextHasErrors
          ? isSingleLine
            ? LineVerificationStatus.ErrorRangeAssertionVerifiedObsolete
            : LineVerificationStatus.ErrorRangeObsolete
          : contextIsPending && !isSingleLine
            ? LineVerificationStatus.Scheduled
            : LineVerificationStatus.VerifiedObsolete,
        CurrentStatus.Verifying => contextHasErrors
          ? isSingleLine
            ? LineVerificationStatus.ErrorRangeAssertionVerifiedVerifying
            : LineVerificationStatus.ErrorRangeVerifying
          : contextIsPending && !isSingleLine ?
            LineVerificationStatus.Verifying
            : LineVerificationStatus.VerifiedVerifying,
        _ => throw new ArgumentOutOfRangeException()
      },
      // We don't display inconclusive on the gutter (user should focus on errors),
      // We display an error range instead
      VerificationStatus.Inconclusive => currentStatus switch {
        CurrentStatus.Current => LineVerificationStatus.ErrorRange,
        CurrentStatus.Obsolete => LineVerificationStatus.ErrorRangeObsolete,
        CurrentStatus.Verifying => LineVerificationStatus.ErrorRangeVerifying,
        _ => throw new ArgumentOutOfRangeException()
      },
      VerificationStatus.Error => currentStatus switch {
        CurrentStatus.Current => isSingleLine ? LineVerificationStatus.Error : LineVerificationStatus.ErrorRange,
        CurrentStatus.Obsolete => isSingleLine
          ? LineVerificationStatus.ErrorObsolete
          : LineVerificationStatus.ErrorRangeObsolete,
        CurrentStatus.Verifying => isSingleLine
          ? LineVerificationStatus.ErrorVerifying
          : LineVerificationStatus.ErrorRangeVerifying,
        _ => throw new ArgumentOutOfRangeException()
      },
      _ => throw new ArgumentOutOfRangeException()
    };
  }

  [TestMethod]
  public void EnsureRenderingIsCoherent() {
    foreach (VerificationStatus verificationStatus in Enum.GetValues(typeof(VerificationStatus))) {
      foreach (CurrentStatus currentStatus in Enum.GetValues(typeof(CurrentStatus))) {
        var isSingleLine = true; do {
          var contextHasError = true; do {
            var contextIsPending = true; do {
              Assert.AreEqual(
                RenderLineVerificationStatusOriginal(isSingleLine, contextHasError, contextIsPending, currentStatus, verificationStatus),
                NodeDiagnostic.RenderLineVerificationStatus(isSingleLine, contextHasError, contextIsPending, currentStatus, verificationStatus)
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