using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics;
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
  /// DTO used to communicate the current verification diagnostics to the LSP client.
  /// </summary>
  [Method(DafnyRequestNames.VerificationDiagnostics, Direction.ServerToClient)]
  public class VerificationDiagnosticsParams : IRequest, IRequest<Unit> {
    public VerificationDiagnosticsParams(DocumentUri uri,
      int version,
      VerificationTree[] verificationTrees,
      Container<Diagnostic> diagnostics,
      int linesCount,
      bool verificationStarted,
      int numberOfResolutionErrors) {
      Uri = uri;
      Version = version;
      VerificationTrees = verificationTrees;
      if (linesCount != 0) { // Deserialization makes linesCount to be equal to zero.
        PerLineDiagnostic =
          RenderPerLineDiagnostics(this, verificationTrees, linesCount, numberOfResolutionErrors, verificationStarted, diagnostics);
      }
    }

    /// <summary>
    /// Gets the URI of the document whose verification completed.
    /// </summary>
    public DocumentUri Uri { get; init; }

    /// <summary>
    /// Gets the version of the document.
    /// </summary>
    public int? Version { get; init; }

    /// <summary>
    /// Returns a tree of diagnostics that can be used
    /// First-level nodes are methods, or witness subset type checks
    /// Second-level nodes are preconditions, postconditions, body verification status
    /// Third level nodes are assertions inside functions 
    /// </summary>
    public VerificationTree[] VerificationTrees { get; init; }

    /// <summary>
    /// Returns per-line real-time diagnostic
    /// </summary>
    public LineVerificationStatus[] PerLineDiagnostic { get; init; }

    static LineVerificationStatus[] RenderPerLineDiagnostics(
      VerificationDiagnosticsParams verificationDiagnosticsParams,
      VerificationTree[] verificationTrees,
      int numberOfLines,
      int numberOfResolutionErrors,
      bool verificationStarted,
      Container<Diagnostic> diagnostics) {
      var result = new LineVerificationStatus[numberOfLines];

      if (verificationTrees.Length == 0 && numberOfResolutionErrors == 0 && verificationStarted) {
        for (var line = 0; line < numberOfLines; line++) {
          result[line] = LineVerificationStatus.Verified;
        }

        return result;
      }

      // Render verification tree content into lines.
      foreach (var verificationTree in verificationTrees) {
        if (verificationTree.Filename == verificationDiagnosticsParams.Uri.GetFileSystemPath() ||
            "untitled:" + verificationTree.Filename == verificationDiagnosticsParams.Uri) {
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

      var resolutionErrorRendered = 0;
      foreach (var diagnostic in diagnostics) {
        if (resolutionErrorRendered >= numberOfResolutionErrors) {
          break;
        }
        if (diagnostic.Range.Start.Line >= 0 && diagnostic.Range.Start.Line < result.Length) {
          result[diagnostic.Range.Start.Line] = LineVerificationStatus.ResolutionError;
          resolutionErrorRendered++;
        }
      }

      var existsErrorRange = false;
      var existsError = false;
      foreach (var line in result) {
        existsErrorRange = existsErrorRange || line == LineVerificationStatus.ErrorContext;
        existsError = existsError || line == LineVerificationStatus.AssertionFailed;
      }

      if (existsErrorRange && !existsError) {
        existsError = false;
      }

      return result;
    }
  }


  public enum VerificationStatus {
    Nothing = 0,
    Verified = 200,
    Inconclusive = 270,
    Error = 400
  }

  public enum CurrentStatus {
    Current = 0,
    Obsolete = 1,
    Verifying = 2
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

  /// <summary>
  /// A verification tree is an abstraction over the code to represent the verification
  /// status of a region of the document, useful for IDE verification inspection.
  /// A verification tree can contain other child trees.
  /// It can currently be rendered linearly, e.g. for gutter display, or used as a tree in a test-like display. 
  /// The verification status consists of two orthogonal concepts:
  /// - StatusVerification: Nothing (initial), Error, Verified, or Inconclusive
  /// - StatusCurrent: Current (Up-to-date), Obsolete (outdated), and Verifying (as notified by the verifier)
  /// </summary>
  /// <param name="DisplayName">A user-facing name of this node, to be displayed in an IDE explorer</param>
  /// <param name="Identifier">A unique identifier, to be used by the IDE to request re-verification</param>
  /// <param name="Filename">The name of the file this region of the document is contained in</param>
  /// <param name="Range">The range of this region of the document</param>
  public record VerificationTree(
     // User-facing name
     string DisplayName,
     // Used to re-trigger the verification of some diagnostics.
     string Identifier,
     string Filename,
     // The range of this node.
     Range Range
  ) {
    // Overriden by checking children if there are some
    public VerificationStatus StatusVerification { get; set; } = VerificationStatus.Nothing;

    // Overriden by checking children if there are some
    public CurrentStatus StatusCurrent { get; set; } = CurrentStatus.Obsolete;

    // Used to relocate a verification tree and to determine which function is currently verifying
    public Position Position => Range.Start;

    /// Time and Resource diagnostics
    public bool Started { get; set; } = false;
    public bool Finished { get; set; } = false;

    /// If this node was an error from a counter-example, RelatedRanges will contain
    /// all the ranges given by the trace of that counter-example
    public ImmutableList<Range> RelatedRanges { get; set; } = ImmutableList<Range>.Empty;

    // Sub-diagnostics if any
    public List<VerificationTree> Children { get; set; } = new();
    private List<VerificationTree> NewChildren { get; set; } = new();

    public int GetNewChildrenCount() {
      return NewChildren.Count;
    }

    public void AddNewChild(VerificationTree newChild) {
      NewChildren.Add(newChild);
    }

    public void SaveNewChildren() {
      Children = NewChildren;
      ResetNewChildren();
    }

    public void ResetNewChildren() {
      NewChildren = new();
    }

    public VerificationTree SetObsolete() {
      if (StatusCurrent != CurrentStatus.Obsolete) {
        StatusCurrent = CurrentStatus.Obsolete;
        foreach (var child in Children) {
          child.SetObsolete();
        }
      }

      return this;
    }

    // Returns true if it started the method, false if it was already started
    public virtual bool Start() {
      if (StatusCurrent != CurrentStatus.Verifying || !Started) {
        StatusCurrent = CurrentStatus.Verifying;
        foreach (var child in Children) {
          child.Start();
        }
        Started = true;
        return true;
      }

      return false;
    }

    // Returns true if it did stop the current node, false if it was already stopped
    public virtual bool Stop() {
      if (StatusCurrent != CurrentStatus.Current || !Finished) {
        StatusCurrent = CurrentStatus.Current;
        foreach (var child in Children) {
          child.Stop();
        }
        Finished = true;
        return true;
      }

      return false;
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

    public static LineVerificationStatus RenderLineVerificationStatus(
      bool isSingleLine, bool contextHasErrors, bool contextIsPending,
      CurrentStatus currentStatus, VerificationStatus verificationStatus) {
      LineVerificationStatus simpleStatus = verificationStatus switch {
        VerificationStatus.Nothing => LineVerificationStatus.Nothing,
        // let's be careful to no display "Verified" for a range if the context does not have errors and is pending
        // because there might be other errors on the same range.
        VerificationStatus.Verified =>
          contextHasErrors
            ? isSingleLine // Sub-implementations that are verified do not count
              ? LineVerificationStatus.AssertionVerifiedInErrorContext
              : LineVerificationStatus.ErrorContext
            : contextIsPending && !isSingleLine
              ? LineVerificationStatus.Nothing
              : LineVerificationStatus.Verified,
        // We don't display inconclusive on the gutter (user should focus on errors),
        // We display an error range instead
        VerificationStatus.Inconclusive =>
          LineVerificationStatus.ErrorContext,
        VerificationStatus.Error => isSingleLine
            ? LineVerificationStatus.AssertionFailed
            : LineVerificationStatus.ErrorContext,
        _ => throw new ArgumentOutOfRangeException()
      };
      return (LineVerificationStatus)((int)simpleStatus + (int)currentStatus);
    }

    // Requires PropagateChildrenErrorsUp to have been called before.
    public virtual void RenderInto(LineVerificationStatus[] perLineDiagnostics, bool contextHasErrors = false, bool contextIsPending = false, Range? otherRange = null, Range? contextRange = null) {
      Range range = otherRange ?? Range;
      var isSingleLine = range.Start.Line == range.End.Line;
      LineVerificationStatus targetStatus = RenderLineVerificationStatus(isSingleLine, contextHasErrors, contextIsPending, StatusCurrent, StatusVerification);
      for (var line = range.Start.Line; line <= range.End.Line; line++) {
        if (line < 0 || perLineDiagnostics.Length <= line) {
          // An error occurred? We don't want null pointer exceptions anyway
          continue;
        }
        if ((int)perLineDiagnostics[line] < (int)(targetStatus)) {
          perLineDiagnostics[line] = targetStatus;
        }
      }
      foreach (var child in Children) {
        child.RenderInto(perLineDiagnostics,
          contextHasErrors || StatusVerification == VerificationStatus.Error,
          contextIsPending ||
            StatusCurrent == CurrentStatus.Obsolete ||
          StatusCurrent == CurrentStatus.Verifying,
          null,
          Range);
      }
      // Ensure that if this is an ImplementationVerificationTree, and children "painted" verified,
      // and this node is still pending
      // at least the first line should show pending.
      if (StatusCurrent == CurrentStatus.Verifying &&
          perLineDiagnostics.ToList().GetRange(range.Start.Line, range.End.Line - range.Start.Line + 1).All(
            line => line == LineVerificationStatus.Verified)) {
        perLineDiagnostics[range.Start.Line] = targetStatus;
      }
    }

    // If the verification never starts on this node, it means there is nothing to verify about it.
    // Returns true if a status was updated
    public bool SetVerifiedIfPending() {
      if (StatusCurrent == CurrentStatus.Obsolete) {
        StatusCurrent = CurrentStatus.Current;
        StatusVerification = VerificationStatus.Verified;
        foreach (var child in Children) {
          child.SetVerifiedIfPending();
        }
        return true;
      }

      return false;
    }

    public virtual VerificationTree GetCopyForNotification() {
      if (Finished) {
        return this;// Won't be modified anymore, no need to duplicate
      }
      return this with {
        Children = Children.Select(child => child.GetCopyForNotification()).ToList()
      };
    }
  }

  public record DocumentVerificationTree(
    string Identifier,
    int Lines
  ) : VerificationTree("Document", Identifier, Identifier,
    new Range(new Position(0, 0),
      new Position(Lines, 0)));

  public record TopLevelDeclMemberVerificationTree(
    string DisplayName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    // The range of this node.
    Range Range
  ) : VerificationTree(DisplayName, Identifier, Filename, Range) {
    // Recomputed from the children which are ImplementationVerificationTree
    public List<AssertionBatchVerificationTree> AssertionBatches { get; set; } = new();

    public override VerificationTree GetCopyForNotification() {
      if (Finished) {
        return this;// Won't be modified anymore, no need to duplicate
      }
      return this with {
        Children = Children.Select(child => child.GetCopyForNotification()).ToList(),
        AssertionBatches = AssertionBatches.Select(child => (AssertionBatchVerificationTree)child.GetCopyForNotification()).ToList()
      };
    }

    public void RecomputeAssertionBatchNodeDiagnostics() {
      var result = new List<AssertionBatchVerificationTree>();
      foreach (var implementationNode in Children.OfType<ImplementationVerificationTree>()) {
        for (var batchIndex = 0; batchIndex < implementationNode.AssertionBatchCount; batchIndex++) {
          var children = implementationNode.Children.OfType<AssertionVerificationTree>().Where(
            assertionNode => assertionNode.AssertionBatchIndex == batchIndex).Cast<VerificationTree>().ToList();
          if (children.Count > 0) {
            var minPosition = children.MinBy(child => child.Position)!.Range.Start;
            var maxPosition = children.MaxBy(child => child.Range.End)!.Range.End;
            result.Add(new AssertionBatchVerificationTree(
              "Assertion batch #" + result.Count,
              "assertion-batch-" + result.Count,
              Filename,
              new Range(minPosition, maxPosition)
            ) {
              Children = children
            });
          }
        }
      }

      AssertionBatches = result;
    }
  }

  // Invariant: There is at least 1 child for every assertion batch
  public record AssertionBatchVerificationTree(
    string DisplayName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    // The range of this node.
    Range Range
  ) : VerificationTree(DisplayName, Identifier, Filename, Range) {
    public override VerificationTree GetCopyForNotification() {
      if (Finished) {
        return this;// Won't be modified anymore, no need to duplicate
      }
      return this with {
        Children = Children.Select(child => child.GetCopyForNotification()).ToList()
      };
    }
  }

  public record ImplementationVerificationTree(
    string DisplayName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    // The range of this node.
    Range Range
  ) : VerificationTree(DisplayName, Identifier, Filename, Range) {
    public int AssertionBatchCount { get; set; }

    private int NewAssertionBatchCount { get; set; }

    public override VerificationTree GetCopyForNotification() {
      if (Finished) {
        return this;// Won't be modified anymore, no need to duplicate
      }
      return this with {
        Children = Children.Select(child => child.GetCopyForNotification()).ToList()
      };
    }

    private Implementation? implementation = null;

    public int GetNewAssertionBatchCount() {
      return NewAssertionBatchCount;
    }

    public override bool Stop() {
      if (base.Stop()) {
        SaveNewChildren();
        return true;
      }

      return false;
    }

    public Implementation? GetImplementation() {
      return implementation;
    }

    public ImplementationVerificationTree WithImplementation(Implementation impl) {
      implementation = impl;
      return this;
    }

    public void IncreaseNewAssertionBatchCount() {
      NewAssertionBatchCount++;
    }
  };

  public record AssertionVerificationTree(
    string DisplayName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    // Used to relocate a assertion verification tree and to determine which function is currently verifying
    Position? SecondaryPosition,
    // The range of this node.
    Range Range
  ) : VerificationTree(DisplayName, Identifier, Filename, Range) {

    // Ranges that should also display an error
    // TODO: Will need to compute this statically for the tests
    public List<Range> ImmediatelyRelatedRanges { get; set; } = new();
    public List<Range> DynamicallyRelatedRanges { get; set; } = new();

    /// <summary>
    /// Which assertion batch this assertion was taken from in its implementation node
    /// </summary>
    public int AssertionBatchIndex { get; init; }

    public AssertionVerificationTree
      WithAssertionAndCounterExample(AssertCmd? inAssertion, Counterexample? inCounterExample) {
      this.assertion = inAssertion;
      this.counterExample = inCounterExample;
      return WithImmediatelyRelatedChanges().WithDynamicallyRelatedChanges();
    }

    private AssertionVerificationTree WithImmediatelyRelatedChanges() {
      if (assertion == null) {
        ImmediatelyRelatedRanges = new();
        return this;
      }

      var tok = assertion.tok;
      var result = new List<Range>();
      while (tok is NestedToken nestedToken) {
        tok = nestedToken.Inner;
        if (tok.filename == assertion.tok.filename) {
          result.Add(tok.GetLspRange());
        }
      }

      if (counterExample is ReturnCounterexample returnCounterexample) {
        tok = returnCounterexample.FailingReturn.tok;
        if (tok.filename == assertion.tok.filename) {
          result.Add(returnCounterexample.FailingReturn.tok.GetLspRange());
        }
      }

      ImmediatelyRelatedRanges = result;
      return this;
    }

    private AssertionVerificationTree WithDynamicallyRelatedChanges() {
      // Ranges that should highlight when stepping on one error.
      if (assertion == null) {
        DynamicallyRelatedRanges = new();
        return this;
      }
      var result = new List<Range>();
      if (counterExample is CallCounterexample callCounterexample) {
        result.Add(callCounterexample.FailingRequires.tok.GetLspRange());
      }
      DynamicallyRelatedRanges = result;
      return this;
    }

    public override void RenderInto(LineVerificationStatus[] perLineDiagnostics, bool contextHasErrors = false,
      bool contextIsPending = false, Range? otherRange = null, Range? contextRange = null) {
      base.RenderInto(perLineDiagnostics, contextHasErrors, contextIsPending, otherRange, contextRange);
      if (StatusVerification == VerificationStatus.Error) {
        foreach (var range in ImmediatelyRelatedRanges) {
          if (contextRange != null && contextRange.Contains(range)) {
            base.RenderInto(perLineDiagnostics, contextHasErrors, contextIsPending, range, contextRange);
          }
        }
      }
    }

    // Contains permanent secondary positions to this node (e.g. return branch positions)
    // Helps to distinguish between assertions with the same position (i.e. ensures for different branches)
    private AssertCmd? assertion;
    private Counterexample? counterExample;


    public AssertCmd? GetAssertion() {
      return assertion;
    }

    public AssertionVerificationTree WithAssertion(AssertCmd cmd) {
      assertion = cmd;
      return this;
    }


    public Counterexample? GetCounterExample() {
      return counterExample;
    }

    public AssertionVerificationTree WithCounterExample(Counterexample? c) {
      counterExample = c;
      return this;
    }
  };
}
