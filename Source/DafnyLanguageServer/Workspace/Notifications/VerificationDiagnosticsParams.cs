using System;
using System.Diagnostics;
using System.Linq;
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

    public bool DiagnosticsAreResolutionErrors { get; init; }

    /// <summary>
    /// Returns per-line real-time diagnostic
    /// </summary>
    public LineVerificationStatus[] PerLineDiagnostic =>
      RenderPerLineDiagnostics(this, PerNodeDiagnostic, LinesCount,
        DiagnosticsAreResolutionErrors, Diagnostics);

    static LineVerificationStatus[] RenderPerLineDiagnostics(
      VerificationDiagnosticsParams verificationDiagnosticsParams,
      NodeDiagnostic[] perNodeDiagnostic,
      int numberOfLines,
      bool diagnosticsAreResolutionErrors,
      Container<Diagnostic> diagnostics
    ) {
      var result = new LineVerificationStatus[numberOfLines];

      // Render node content into lines.
      foreach (var nodeDiagnostic in perNodeDiagnostic) {
        if (nodeDiagnostic.Filename == verificationDiagnosticsParams.Uri) {
          nodeDiagnostic.RenderInto(result);
        }
      }

      // Fill in the missing "Unknown" based on the surrounding content
      // The filling only takes Verified an Error
      var previousNotUnknown = result.FirstOrDefault(
        status => status != LineVerificationStatus.Unknown
        , LineVerificationStatus.Unknown);
      for (var i = 0; i < numberOfLines; i++) {
        if (previousNotUnknown != LineVerificationStatus.Verified &&
            previousNotUnknown != LineVerificationStatus.ErrorRange) {
          previousNotUnknown = LineVerificationStatus.Unknown;
        }
        if (result[i] == LineVerificationStatus.Unknown) {
          result[i] = previousNotUnknown;
        } else {
          previousNotUnknown = result[i];

        }
      }

      if (diagnosticsAreResolutionErrors) {
        foreach (var diagnostic in diagnostics) {
          result[diagnostic.Range.Start.Line - 1] = LineVerificationStatus.ResolutionError;
        }
      }

      return result;
    }
  }

  public enum NodeVerificationStatus {
    Unknown = 0,
    Obsolete = 1,
    Pending = 2,
    Verified = 3,
    ErrorObsolete = 4,
    ErrorPending = 5,
    Error = 6
  }

  public enum LineVerificationStatus {
    // Default value for every line, before the renderer figures it out.
    Unknown = 0,
    // For first-time computation not actively computing but soon
    // (scheduledComputation)
    Obsolete = 1,
    // For first-time computations, actively computing
    Pending = 2,
    // Also applicable for empty spaces if they are not surrounded by errors. 
    Verified = 3,
    // For containers of other diagnostics nodes (e.g. methods)
    ErrorRangeObsolete = 4,
    ErrorRangePending = 5,
    ErrorRange = 6,
    // For specific lines which have errors on it.
    ErrorObsolete = 7,
    ErrorPending = 8,
    Error = 9,
    // For lines containing resolution or parse errors
    ResolutionError = 10
  }

  public class NodeDiagnostic {
    /// User-facing name
    public string DisplayName { get; init; }

    /// Used to relocate previous diagnostics, and re-trigger the verification of some diagnostics.
    public string Identifier { get; init; }

    public string Filename { get; init; }

    public Position Position { get; init; }

    /// Time and Resource diagnostics
    public bool Started { get; private set; } = false;

    public bool Finished { get; private set; } = false;
    public int StartTime { get; private set; }

    public void Start() {
      StartTime = DateTime.Now.Millisecond;
      Status = Status == NodeVerificationStatus.Error ? NodeVerificationStatus.ErrorPending :
          Status == NodeVerificationStatus.Verified ? Status :
          NodeVerificationStatus.Pending;
      Started = true;
    }

    public void Stop() {
      EndTime = DateTime.Now.Millisecond;
      Finished = true;
    }

    public int EndTime { get; private set; }

    public int TimeSpent => Finished ? EndTime - StartTime : Started ? DateTime.Now.Millisecond - StartTime : -1;

    // Resources allocated at the end of the computation.
    public int ResourceCount { get; set; } = -1;

    // The range of this node.
    public Range Range { get; init; }

    // Sub-diagnostics if any
    public NodeDiagnostic[] Children { get; set; } = Array.Empty<NodeDiagnostic>();

    // Overriden by checking children if there are some
    public NodeVerificationStatus Status { get; set; } = NodeVerificationStatus.Obsolete;

    private static int StatusSeverityOf(NodeVerificationStatus status) {
      return (int)status;
    }
    private static int StatusSeverityOf(LineVerificationStatus status) {
      return (int)status;
    }

    public void RecomputeStatus() {
      var childrenStatus = NodeVerificationStatus.Verified;
      var severity = StatusSeverityOf(childrenStatus);
      foreach (var child in Children) {
        child.RecomputeStatus();
        var childSeverity = StatusSeverityOf(child.Status);
        if (childSeverity > severity) {
          childrenStatus = child.Status;
        }
      }

      if (childrenStatus != NodeVerificationStatus.Verified) {
        Status = childrenStatus;
      }
    }

    public void RenderInto(LineVerificationStatus[] perLineDiagnostics) {
      foreach (var child in Children) {
        child.RenderInto(perLineDiagnostics);
      }
      for (var line = Range.Start.Line - 1; line <= Range.End.Line - 1; line++) {
        if (StatusSeverityOf(perLineDiagnostics[line]) < StatusSeverityOf(Status)) {
          if (Children.Length == 0) { // Not a range
            perLineDiagnostics[line] = Status switch {
              NodeVerificationStatus.Error => LineVerificationStatus.Error,
              NodeVerificationStatus.ErrorPending => LineVerificationStatus.ErrorPending,
              NodeVerificationStatus.ErrorObsolete => LineVerificationStatus.ErrorObsolete,
              var status => (LineVerificationStatus)(int)status
            };
          } else { // For a range, 
            perLineDiagnostics[line] = Status switch {
              NodeVerificationStatus.Error => LineVerificationStatus.ErrorRange,
              NodeVerificationStatus.ErrorPending => LineVerificationStatus.ErrorRangePending,
              NodeVerificationStatus.ErrorObsolete => LineVerificationStatus.ErrorRangeObsolete,
              var status => (LineVerificationStatus)(int)status
            };
          }
        }
      }
    }

    // Returns true if a status was updated
    public bool SetVerifiedIfPending() {
      if (Status is NodeVerificationStatus.Obsolete or NodeVerificationStatus.ErrorObsolete) {
        Status = NodeVerificationStatus.Verified;
        return true;
      }

      return false;
    }
  }
}
