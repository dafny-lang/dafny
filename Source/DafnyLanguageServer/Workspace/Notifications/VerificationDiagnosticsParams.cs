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
          result[diagnostic.Range.Start.Line] = LineVerificationStatus.ResolutionError;
        }
      }

      return result;
    }
  }

  public enum NodeVerificationStatus {
    Unknown = 0,
    Scheduled = 1,
    Verifying = 2,
    VerifiedObsolete = 3,
    VerifiedVerifying = 4,
    Verified = 5,
    ErrorObsolete = 6,
    ErrorVerifying = 7,
    Error = 8
  }

  public enum LineVerificationStatus {
    // Default value for every line, before the renderer figures it out.
    Unknown = 0,
    // For first-time computation not actively computing but soon
    // (scheduledComputation)
    Scheduled = 1,
    // For first-time computations, actively computing
    Verifying = 2,
    VerifiedObsolete = 3,
    VerifiedVerifying = 4,
    // Also applicable for empty spaces if they are not surrounded by errors. 
    Verified = 5,
    // For containers of other diagnostics nodes (e.g. methods)
    ErrorRangeObsolete = 6,
    ErrorRangePending = 7,
    ErrorRange = 8,
    // For specific lines which have errors on it.
    ErrorObsolete = 9,
    ErrorVerifying = 10,
    Error = 11,
    // For lines containing resolution or parse errors
    ResolutionError = 12
  }

  public class NodeDiagnostic {
    /// User-facing name
    public string DisplayName { get; init; }

    /// Used to relocate previous diagnostics, and re-trigger the verification of some diagnostics.
    public string Identifier { get; init; }

    public string Filename { get; init; }

    public Position Position { get; set; }

    /// Time and Resource diagnostics
    public bool Started { get; private set; } = false;

    public bool Finished { get; private set; } = false;
    public int StartTime { get; private set; }
    public int EndTime { get; private set; }
    public int TimeSpent => Finished ? EndTime - StartTime : Started ? DateTime.Now.Millisecond - StartTime : -1;

    // Resources allocated at the end of the computation.
    public int ResourceCount { get; set; } = -1;

    // The range of this node. Make it a record to remove the set
    public Range Range { get; set; }

    // Sub-diagnostics if any
    public NodeDiagnostic[] Children { get; set; } = Array.Empty<NodeDiagnostic>();

    // Overriden by checking children if there are some
    public NodeVerificationStatus Status { get; set; } = NodeVerificationStatus.Scheduled;

    public NodeDiagnostic SetObsolete() {
      Status = Status switch {
        NodeVerificationStatus.Error => NodeVerificationStatus.ErrorObsolete,
        NodeVerificationStatus.Verified => NodeVerificationStatus.VerifiedObsolete,
        NodeVerificationStatus.Verifying => NodeVerificationStatus.Scheduled,
        NodeVerificationStatus.ErrorVerifying => NodeVerificationStatus.ErrorObsolete,
        NodeVerificationStatus.VerifiedVerifying => NodeVerificationStatus.VerifiedObsolete,
        NodeVerificationStatus.Scheduled => NodeVerificationStatus.Scheduled,
        NodeVerificationStatus.Unknown => NodeVerificationStatus.Unknown,
        _ => Status
      };
      foreach (var child in Children) {
        child.SetObsolete();
      }

      return this;
    }

    public void Start() {
      StartTime = DateTime.Now.Millisecond;
      Status = Status == NodeVerificationStatus.Error ? NodeVerificationStatus.ErrorVerifying :
        Status == NodeVerificationStatus.Verified ? Status :
        NodeVerificationStatus.Verifying;
      Started = true;
    }

    public void Stop() {
      EndTime = DateTime.Now.Millisecond;
      Finished = true;
    }
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
              NodeVerificationStatus.ErrorVerifying => LineVerificationStatus.ErrorVerifying,
              NodeVerificationStatus.ErrorObsolete => LineVerificationStatus.ErrorObsolete,
              NodeVerificationStatus.VerifiedObsolete => LineVerificationStatus.VerifiedObsolete,
              NodeVerificationStatus.VerifiedVerifying => LineVerificationStatus.VerifiedVerifying,
              NodeVerificationStatus.Scheduled => LineVerificationStatus.Scheduled,
              NodeVerificationStatus.Verifying => LineVerificationStatus.Verifying,
              var status => (LineVerificationStatus)(int)status
            };
          } else { // For a range, 
            perLineDiagnostics[line] = Status switch {
              NodeVerificationStatus.Error => LineVerificationStatus.ErrorRange,
              NodeVerificationStatus.ErrorVerifying => LineVerificationStatus.ErrorRangePending,
              NodeVerificationStatus.ErrorObsolete => LineVerificationStatus.ErrorRangeObsolete,
              NodeVerificationStatus.VerifiedObsolete => LineVerificationStatus.VerifiedObsolete,
              NodeVerificationStatus.VerifiedVerifying => LineVerificationStatus.VerifiedVerifying,
              NodeVerificationStatus.Scheduled => LineVerificationStatus.Scheduled,
              NodeVerificationStatus.Verifying => LineVerificationStatus.Verifying,
              var status => (LineVerificationStatus)(int)status
            };
          }
        }
      }
    }

    // Returns true if a status was updated
    public bool SetVerifiedIfPending() {
      if (Status is NodeVerificationStatus.Scheduled or NodeVerificationStatus.ErrorObsolete) {
        Status = NodeVerificationStatus.Verified;
        return true;
      }

      return false;
    }
  }
}
