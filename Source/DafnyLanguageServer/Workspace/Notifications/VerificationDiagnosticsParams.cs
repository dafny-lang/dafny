using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection.Metadata;
using MediatR;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

#pragma warning disable CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider declaring as nullable.

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// Contains information about the state of verification for each line in a file
  /// </summary>
  [Method(DafnyRequestNames.VerificationStatusGutter, Direction.ServerToClient)]
  public record VerificationStatusGutter(
    DocumentUri Uri,
    int? Version,
    LineVerificationStatus[] PerLineStatus
    ) : IRequest {

    public static VerificationStatusGutter ComputeFrom(
        DocumentUri uri,
        int version,
        VerificationTree[] verificationTrees,
        Container<Diagnostic> diagnostics,
        int linesCount,
        bool verificationStarted) {
      var perLineStatus = RenderPerLineDiagnostics(uri, verificationTrees, linesCount, verificationStarted, diagnostics);
      return new VerificationStatusGutter(uri, version, perLineStatus);
    }

    public static LineVerificationStatus[] RenderPerLineDiagnostics(
      DocumentUri uri,
      VerificationTree[] verificationTrees,
      int numberOfLines,
      bool verificationStarted,
      Container<Diagnostic> parseAndResolutionErrors) {
      var result = new LineVerificationStatus[numberOfLines];

      if (verificationTrees.Length == 0 && !parseAndResolutionErrors.Any() && verificationStarted) {
        for (var line = 0; line < numberOfLines; line++) {
          result[line] = LineVerificationStatus.Verified;
        }

        return result;
      }

      // Render verification tree content into lines.
      foreach (var verificationTree in verificationTrees) {
        if (verificationTree.Filename == uri.GetFileSystemPath() ||
            "untitled:" + verificationTree.Filename == uri) {
          verificationTree.RenderInto(result);
        }
      }

      // Fill in the missing "Unknown" based on the surrounding content
      // The filling only takes Verified an Error
      var previousNotUnknown = LineVerificationStatus.Nothing;
      var lineDelta = 1;
      // Two passes so that we can fill gaps based on what happened before AND after
      for (var line = 0; 0 <= line; line += lineDelta) {
        if (line == numberOfLines) {
          lineDelta = -1;
          previousNotUnknown = LineVerificationStatus.Nothing;
          continue;
        }
        if (previousNotUnknown != LineVerificationStatus.Verified &&
            previousNotUnknown != LineVerificationStatus.VerifiedObsolete &&
            previousNotUnknown != LineVerificationStatus.VerifiedVerifying) {
          previousNotUnknown = LineVerificationStatus.Nothing;
        }
        if (result[line] == LineVerificationStatus.Nothing) {
          result[line] = previousNotUnknown;
        } else {
          previousNotUnknown = result[line];
        }
      }

      foreach (var diagnostic in parseAndResolutionErrors) {
        if (diagnostic.Range.Start.Line >= 0 && diagnostic.Range.Start.Line < result.Length) {
          result[diagnostic.Range.Start.Line] = LineVerificationStatus.ResolutionError;
        }
      }
      return result;
    }
  }

  public enum LineVerificationStatus {
    // Default value for every line, before the renderer figures it out.
    Nothing = 0,
    // For first-time computation not actively computing but soon. Synonym of "obsolete"
    // (scheduledComputation)
    Scheduled = 1,
    // For first-time computations, actively computing
    Verifying = 2,
    VerifiedObsolete = 201,
    VerifiedVerifying = 202,
    // Also applicable for empty spaces if they are not surrounded by errors.
    Verified = 200,
    // For trees containing children with errors (e.g. functions, methods, fields, subset types)
    ErrorContextObsolete = 301,
    ErrorContextVerifying = 302,
    ErrorContext = 300,
    // For individual assertions in error contexts
    AssertionVerifiedInErrorContextObsolete = 351,
    AssertionVerifiedInErrorContextVerifying = 352,
    AssertionVerifiedInErrorContext = 350,
    // For specific lines which have errors on it. They take over verified assertions
    AssertionFailedObsolete = 401,
    AssertionFailedVerifying = 402,
    AssertionFailed = 400,
    // For lines containing resolution or parse errors
    ResolutionError = 500
  }
}
