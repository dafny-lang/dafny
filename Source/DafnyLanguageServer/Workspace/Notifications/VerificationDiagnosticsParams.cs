using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Reflection.Metadata;
using MediatR;
using Microsoft.Boogie;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

#pragma warning disable CS8618 // Non-nullable field must contain a non-null value when exiting constructor. Consider declaring as nullable.

namespace Microsoft.Dafny.LanguageServer.Workspace.Notifications {
  /// <summary>
  /// DTO used to communicate the current compilation status to the LSP client.
  /// </summary>
  [Method(DafnyRequestNames.VerificationDiagnostics, Direction.ServerToClient)]
  public class VerificationDiagnosticsParams : IRequest, IRequest<Unit> {
    /// <summary>
    /// Gets the URI of the document whose verification completed.
    /// </summary>
    public DocumentUri Uri { get; init; }

    /// <summary>
    /// Gets the version of the document.
    /// </summary>
    public int? Version { get; init; }

    /// <summary>
    /// Gets the same diagnostics as displayed in the diagnostics window
    /// </summary>
    public Container<Diagnostic> Diagnostics { get; init; }

    /// <summary>
    /// Returns a tree of diagnostics that can be used
    /// First-level nodes are methods, or witness subset type checks
    /// Second-level nodes are preconditions, postconditions, body verification status
    /// Third level nodes are assertions inside functions 
    /// </summary>
    public NodeDiagnostic[] PerNodeDiagnostic { get; init; }

    /// <summary>
    /// The number of lines in the document
    /// </summary>
    public int LinesCount { get; init; }

    public int NumberOfResolutionErrors { get; init; }

    /// <summary>
    /// Returns per-line real-time diagnostic
    /// </summary>
    public LineVerificationStatus[] PerLineDiagnostic =>
      RenderPerLineDiagnostics(this, PerNodeDiagnostic, LinesCount,
        NumberOfResolutionErrors, Diagnostics);

    static LineVerificationStatus[] RenderPerLineDiagnostics(
      VerificationDiagnosticsParams verificationDiagnosticsParams,
      NodeDiagnostic[] perNodeDiagnostic,
      int numberOfLines,
      int numberOfResolutionErrors,
      Container<Diagnostic> diagnostics
    ) {
      var result = new LineVerificationStatus[numberOfLines];

      // Render node content into lines.
      foreach (var nodeDiagnostic in perNodeDiagnostic) {
        if (nodeDiagnostic.Filename == verificationDiagnosticsParams.Uri.GetFileSystemPath() ||
            "untitled:" + nodeDiagnostic.Filename == verificationDiagnosticsParams.Uri) {
          nodeDiagnostic.RenderInto(result);
        }
      }

      // Fill in the missing "Unknown" based on the surrounding content
      // The filling only takes Verified an Error
      var previousNotUnknown = LineVerificationStatus.Unknown;
      var lineDelta = 1;
      // Two passes so that we can fill gaps based on what happened before AND after
      for (var line = 0; 0 <= line; line += lineDelta) {
        if (line == numberOfLines) {
          lineDelta = -1;
          previousNotUnknown = LineVerificationStatus.Unknown;
          continue;
        }
        if (previousNotUnknown != LineVerificationStatus.Verified &&
            previousNotUnknown != LineVerificationStatus.VerifiedObsolete &&
            previousNotUnknown != LineVerificationStatus.VerifiedVerifying) {
          previousNotUnknown = LineVerificationStatus.Unknown;
        }
        if (result[line] == LineVerificationStatus.Unknown) {
          result[line] = previousNotUnknown;
        } else {
          previousNotUnknown = result[line];
        }
      }

      var resolutionErrorRendered = 0;
      foreach (var diagnostic in diagnostics) {
        if (resolutionErrorRendered >= numberOfResolutionErrors) {
          break;
        }
        result[diagnostic.Range.Start.Line] = LineVerificationStatus.ResolutionError;
        resolutionErrorRendered++;
      }

      CheckResult(result);

      return result;
    }

    // Given a rendering, verifies that there is no error next to a verified, it should always be after an errorRange
    private static void CheckResult(LineVerificationStatus[] result) {
      var previousStatus = LineVerificationStatus.Verified;
      foreach (var status in result) {
        if (previousStatus is LineVerificationStatus.Verified or LineVerificationStatus.VerifiedObsolete
            or LineVerificationStatus.VerifiedVerifying &&
            status is LineVerificationStatus.Error or LineVerificationStatus.ErrorObsolete or LineVerificationStatus.ErrorVerifying
            ) {
          break;
        }

        previousStatus = status;
      }
    }
  }


  public enum VerificationStatus {
    Unknown = 0,
    Verified = 200,
    Error = 400
  }

  public enum CurrentStatus {
    Current = 0,
    Obsolete = 1,
    Verifying = 2
  }

  public enum LineVerificationStatus {
    // Default value for every line, before the renderer figures it out.
    Unknown = 0,
    // For first-time computation not actively computing but soon. Synonym of "obsolete"
    // (scheduledComputation)
    Scheduled = 1,
    // For first-time computations, actively computing
    Verifying = 2,
    VerifiedObsolete = 201,
    VerifiedVerifying = 202,
    // Also applicable for empty spaces if they are not surrounded by errors.
    Verified = 200,
    // For containers of other diagnostics nodes (e.g. methods)
    ErrorRangeObsolete = 301,
    ErrorRangeVerifying = 302,
    ErrorRange = 300,
    // For individual assertions in error ranges
    ErrorRangeAssertionVerifiedObsolete = 351,
    ErrorRangeAssertionVerifiedVerifying = 352,
    ErrorRangeAssertionVerified = 350,
    // For specific lines which have errors on it. They take over verified assertions
    ErrorObsolete = 401,
    ErrorVerifying = 402,
    Error = 400,
    // For lines containing resolution or parse errors
    ResolutionError = 16
  }

  public abstract record NodeDiagnostic(
     /// User-facing name
     string DisplayName,
     /// Used to re-trigger the verification of some diagnostics.
     string Identifier,
     string Filename,
     // Used to relocate a node diagnostic and to determine which function is currently verifying
     Position Position,
     // The range of this node.
     Range Range
  ) {
    /// Time and Resource diagnostics
    public bool Started { get; set; } = false;
    public bool Finished { get; set; } = false;
    public DateTime StartTime { get; private set; }
    public DateTime EndTime { get; private set; }
    public int TimeSpent => (int)(Finished ? ((TimeSpan)(EndTime - StartTime)).TotalMilliseconds : Started ? (DateTime.Now - StartTime).TotalMilliseconds : 0);
    // Resources allocated at the end of the computation.
    public int ResourceCount { get; set; } = 0;



    // If this node is an error, all the trace positions
    public List<Range> RelatedRanges { get; set; } = new();

    // Sub-diagnostics if any
    public List<NodeDiagnostic> Children { get; set; } = new();
    private List<NodeDiagnostic> NewChildren { get; set; } = new();

    public int GetNewChildrenCount() {
      return NewChildren.Count;
    }

    public void AddNewChild(NodeDiagnostic newChild) {
      NewChildren.Add(newChild);
    }

    public void SaveNewChildren() {
      Children = NewChildren;
      ResetNewChildren();
    }
    public void ResetNewChildren() {
      NewChildren = new();
    }

    // Overriden by checking children if there are some
    public VerificationStatus StatusVerification { get; set; } = VerificationStatus.Unknown;

    // Overriden by checking children if there are some
    public CurrentStatus StatusCurrent { get; set; } = CurrentStatus.Obsolete;

    public NodeDiagnostic SetObsolete() {
      if (StatusCurrent != CurrentStatus.Obsolete) {
        StatusCurrent = CurrentStatus.Obsolete;
        foreach (var child in Children) {
          child.SetObsolete();
        }
      }

      return this;
    }

    public virtual void Start() {
      if (StatusCurrent != CurrentStatus.Verifying || !Started) {
        StartTime = DateTime.Now;
        StatusCurrent = CurrentStatus.Verifying;
        foreach (var child in Children) {
          child.Start();
        }
        Started = true;
      }
    }

    public void Stop() {
      if (StatusCurrent != CurrentStatus.Current || !Finished) {
        EndTime = DateTime.Now;
        StatusCurrent = CurrentStatus.Current;
        foreach (var child in Children) {
          child.Stop();
        }
        Finished = true;
      }
    }

    public void PropagateChildrenErrorsUp() {
      var childrenHaveErrors = false;
      foreach (var child in Children) {
        child.PropagateChildrenErrorsUp();
        if (child.StatusVerification == VerificationStatus.Error) {
          childrenHaveErrors = true;
        }
      }

      if (childrenHaveErrors) {
        StatusVerification = VerificationStatus.Error;
      }
    }

    // Requires PropagateChildrenErrorsUp to have been called before.
    public void RenderInto(LineVerificationStatus[] perLineDiagnostics, bool contextHasErrors = false) {
      var isSingleLine = Range.Start.Line == Range.End.Line;
      // First render the node.
      for (var line = Range.Start.Line - 1; line <= Range.End.Line - 1; line++) {
        LineVerificationStatus targetStatus = StatusVerification switch {
          VerificationStatus.Unknown => StatusCurrent switch {
            CurrentStatus.Current => LineVerificationStatus.Unknown,
            CurrentStatus.Obsolete => LineVerificationStatus.Scheduled,
            CurrentStatus.Verifying => LineVerificationStatus.Verifying,
            _ => throw new ArgumentOutOfRangeException()
          },
          VerificationStatus.Verified => StatusCurrent switch {
            CurrentStatus.Current => contextHasErrors
              ? LineVerificationStatus.ErrorRangeAssertionVerified
              : LineVerificationStatus.Verified,
            CurrentStatus.Obsolete => contextHasErrors
              ? LineVerificationStatus.ErrorRangeAssertionVerifiedObsolete
              : LineVerificationStatus.VerifiedObsolete,
            CurrentStatus.Verifying => contextHasErrors
              ? LineVerificationStatus.ErrorRangeAssertionVerifiedVerifying
              : LineVerificationStatus.VerifiedVerifying,
            _ => throw new ArgumentOutOfRangeException()
          },
          VerificationStatus.Error => StatusCurrent switch {
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
        if ((int)perLineDiagnostics[line] < (int)(targetStatus)) {
          perLineDiagnostics[line] = targetStatus;
        }
      }
      foreach (var child in Children) {
        child.RenderInto(perLineDiagnostics,
          contextHasErrors || StatusVerification == VerificationStatus.Error);
      }
    }

    // If the verification never starts on this node, it means there is nothing to verify about it.
    // Returns true if a status was updated
    public bool SetVerifiedIfPending() {
      if (StatusCurrent == CurrentStatus.Obsolete) {
        StatusCurrent = CurrentStatus.Current;
        StatusVerification = VerificationStatus.Verified;
        return true;
      }

      return false;
    }
  }

  public sealed record DocumentNodeDiagnostic(
    string Identifier,
    int Lines
  ) : NodeDiagnostic("Document", Identifier, Identifier,
    new Position(0, 0), new Range(new Position(0, 0),
      new Position(Lines, 0)));

  public sealed record MethodOrSubsetTypeNodeDiagnostic(
    string DisplayName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    // Used to relocate a node diagnostic and to determine which function is currently verifying
    Position Position,
    // The range of this node.
    Range Range
  ) : NodeDiagnostic(DisplayName, Identifier, Filename, Position, Range) {
    public List<int> AssertionBatchTimes =>
      Children.OfType<ImplementationNodeDiagnostic>().SelectMany(child => child.AssertionBatchTimes).ToList();

    public int AssertionBatchCount => AssertionBatchTimes.Count;
    public int LongestAssertionBatchTime {
      get {
        var assertionBatchTimes = AssertionBatchTimes;
        return assertionBatchTimes.Count == 0 ? 0 : assertionBatchTimes.Max();
      }
    }

    public int LongestAssertionBatchTimeIndex {
      get {
        var longestAssertionBatchTimes = LongestAssertionBatchTime;
        return longestAssertionBatchTimes != 0 ? AssertionBatchTimes.IndexOf(longestAssertionBatchTimes) : -1;
      }
    }

  }

  public sealed record ImplementationNodeDiagnostic(
    string DisplayName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    // Used to relocate a node diagnostic and to determine which function is currently verifying
    Position Position,
    // The range of this node.
    Range Range
  ) : NodeDiagnostic(DisplayName, Identifier, Filename, Position, Range) {
    public List<int> AssertionBatchTimes { get; set; } = new();
    public List<int> AssertionBatchCounts { get; set; } = new();

    public int SplitCount => AssertionBatchTimes.Count;

    private Implementation? implementation = null;

    public override void Start() {
      base.Start();
      AssertionBatchTimes = new();
      AssertionBatchCounts = new();
    }

    public Implementation? GetImplementation() {
      return implementation;
    }

    public ImplementationNodeDiagnostic WithImplementation(Implementation impl) {
      implementation = impl;
      return this;
    }
  };

  public sealed record AssertionNodeDiagnostic(
    string DisplayName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    // Used to relocate a node diagnostic and to determine which function is currently verifying
    Position Position,
    Position? SecondaryPosition,
    // The range of this node.
    Range Range
  ) : NodeDiagnostic(DisplayName, Identifier, Filename, Position, Range) {
    // Contains permanent secondary positions to this node (e.g. return branch positions)
    // Helps to distinguish between assertions with the same position (i.e. ensures for different branches)
    private AssertCmd? assertion = null;

    /// <summary>
    /// Which split this assertion was taken from
    /// </summary>
    public int SplitNumber { get; set; }

    /// <summary>
    /// 0-based position of the assertion it is in the assertion batch
    /// </summary>
    public int AssertionNumber { get; set; }

    public AssertCmd? GetAssertion() {
      return assertion;
    }

    public AssertionNodeDiagnostic WithAssertion(AssertCmd cmd) {
      assertion = cmd;
      return this;
    }
  };
}
