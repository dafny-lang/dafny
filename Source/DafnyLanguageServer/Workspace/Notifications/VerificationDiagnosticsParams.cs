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

      if (diagnosticsAreResolutionErrors) {
        foreach (var diagnostic in diagnostics) {
          result[diagnostic.Range.Start.Line] = LineVerificationStatus.ResolutionError;
        }
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

  public enum NodeVerificationStatus {
    Unknown = 0,
    Scheduled = 1,
    Verifying = 2,
    VerifiedObsolete = 3,
    VerifiedVerifying = 4,
    Verified = 5,
    Inconclusive = 6,
    ErrorObsolete = 7,
    ErrorVerifying = 8,
    Error = 9
  }

  public enum LineVerificationStatus {
    // Default value for every line, before the renderer figures it out.
    Unknown = 0,
    // For first-time computation not actively computing but soon. Synonym of "obsolete"
    // (scheduledComputation)
    Scheduled = 1,
    // For first-time computations, actively computing
    Verifying = 2,
    VerifiedObsolete = 3,
    VerifiedVerifying = 4,
    // Also applicable for empty spaces if they are not surrounded by errors. 
    Verified = 5,
    // Dafny tried to do something but couldn't (timeout, out of resources...)
    Inconclusive = 6,
    // For containers of other diagnostics nodes (e.g. methods)
    ErrorRangeObsolete = 7,
    ErrorRangeVerifying = 8,
    ErrorRange = 9,
    // For individual assertions in error ranges
    ErrorRangeAssertionVerifiedObsolete = 10,
    ErrorRangeAssertionVerifiedVerifying = 11,
    ErrorRangeAssertionVerified = 12,
    // For specific lines which have errors on it.
    ErrorObsolete = 13,
    ErrorVerifying = 14,
    Error = 15,
    // For lines containing resolution or parse errors
    ResolutionError = 16
  }

  public record NodeDiagnostic(
     /// User-facing name
     string DisplayName,
     /// Used to re-trigger the verification of some diagnostics.
     string Identifier,
     string Filename,
     // Used to relocate a node diagnostic and to determine which function is currently verifying
     Position Position,
     // The range of this node.
     Range Range,
     // True if this node is only gathering children feedback.
     bool IsAlwaysRange
  ) {
    /// Time and Resource diagnostics
    public bool Started { get; private set; } = false;
    public bool Finished { get; private set; } = false;
    public DateTime StartTime { get; private set; }
    public DateTime EndTime { get; private set; }
    public int TimeSpent => (int)(Finished ? ((TimeSpan)(EndTime - StartTime)).TotalMilliseconds : Started ? (DateTime.Now - StartTime).TotalMilliseconds : 0);
    public int MaximumChildTimeSpent => Children.Any() ? Children.Max(child => child.TimeSpent) : TimeSpent;
    // Resources allocated at the end of the computation.

    public int ResourceCount { get; set; } = 0;

    // Sub-diagnostics if any
    public List<NodeDiagnostic> Children { get; set; } = new();
    private List<NodeDiagnostic> NewChildren { get; set; } = new();

    public int NewChildrenCount => NewChildren.Count;
    public void AddNewChild(NodeDiagnostic newChild) {
      NewChildren.Add(newChild);
    }

    public List<NodeDiagnostic> CurrentNewChildren => NewChildren;

    public void SaveNewChildren() {
      Children = NewChildren;
      ResetNewChildren();
    }
    public void ResetNewChildren() {
      NewChildren = new();
    }

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
      StartTime = DateTime.Now;
      Status = Status is NodeVerificationStatus.Error or NodeVerificationStatus.ErrorObsolete ? NodeVerificationStatus.ErrorVerifying :
        Status is NodeVerificationStatus.Verified or NodeVerificationStatus.VerifiedObsolete ? NodeVerificationStatus.VerifiedVerifying :
        NodeVerificationStatus.Verifying;
      // Until we can track children, if some children were obsolete, should be "Verifying"
      foreach (var child in Children) {
        child.Start();
      }
      Started = true;
    }

    public void Stop() {
      EndTime = DateTime.Now;
      foreach (var child in Children) {
        child.Stop();
      }
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

    public void RenderInto(LineVerificationStatus[] perLineDiagnostics, bool contextHasErrors = false) {
      foreach (var child in Children) {
        child.RenderInto(perLineDiagnostics, IsStatusError());
      }
      for (var line = Range.Start.Line - 1; line <= Range.End.Line - 1; line++) {
        LineVerificationStatus targetStatus;
        switch (Status) {
          case NodeVerificationStatus.Verified when contextHasErrors:
            targetStatus = LineVerificationStatus.ErrorRangeAssertionVerified;
            break;
          case NodeVerificationStatus.Verifying when contextHasErrors:
            targetStatus = LineVerificationStatus.ErrorRangeAssertionVerifiedVerifying;
            break;
          case NodeVerificationStatus.VerifiedObsolete when contextHasErrors:
            targetStatus = LineVerificationStatus.ErrorRangeAssertionVerifiedObsolete;
            break;
          default: {
              if (Children.Count == 0 && !IsAlwaysRange) { // Not a range
                targetStatus = Status switch {
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
                targetStatus = Status switch {
                  NodeVerificationStatus.Error => LineVerificationStatus.ErrorRange,
                  NodeVerificationStatus.ErrorVerifying => LineVerificationStatus.ErrorRangeVerifying,
                  NodeVerificationStatus.ErrorObsolete => LineVerificationStatus.ErrorRangeObsolete,
                  NodeVerificationStatus.VerifiedObsolete => LineVerificationStatus.VerifiedObsolete,
                  NodeVerificationStatus.VerifiedVerifying => LineVerificationStatus.VerifiedVerifying,
                  NodeVerificationStatus.Scheduled => LineVerificationStatus.Scheduled,
                  NodeVerificationStatus.Verifying => LineVerificationStatus.Verifying,
                  var status => (LineVerificationStatus)(int)status
                };
              }

              break;
            }
        }
        if (StatusSeverityOf(perLineDiagnostics[line]) < StatusSeverityOf(targetStatus)) {
          perLineDiagnostics[line] = targetStatus;
        }
      }
    }

    private bool IsStatusError() {
      return Status == NodeVerificationStatus.Error ||
             Status == NodeVerificationStatus.Inconclusive ||
             Status == NodeVerificationStatus.ErrorObsolete ||
             Status == NodeVerificationStatus.ErrorVerifying;
    }

    // Returns true if a status was updated
    public bool SetVerifiedIfPending() {
      if (Status is NodeVerificationStatus.Scheduled or NodeVerificationStatus.ErrorObsolete or NodeVerificationStatus.VerifiedObsolete) {
        Status = NodeVerificationStatus.Verified;
        return true;
      }

      return false;
    }

    private Implementation? implementation = null;

    public Implementation? GetImplementation() {
      return implementation;
    }

    public NodeDiagnostic WithImplementation(Implementation impl) {
      implementation = impl;
      return this;
    }
  }
}
