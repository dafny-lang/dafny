﻿using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection.Metadata;
using DafnyCore.Verifier;
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
  [Method(DafnyRequestNames.VerificationStatusGutter, Direction.ServerToClient)]
  public record VerificationStatusGutter(
    DocumentUri Uri,
    int? Version,
    LineVerificationStatus[] PerLineStatus
    ) : IRequest {

    public static VerificationStatusGutter ComputeFrom(
        DocumentUri uri,
        int? version,
        ICollection<VerificationTree> verificationTrees,
        Container<Diagnostic> resolutionErrors,
        int linesCount,
        bool verificationStarted) {
      var perLineStatus = RenderPerLineDiagnostics(uri, verificationTrees, linesCount, verificationStarted, resolutionErrors);
      return new VerificationStatusGutter(uri, version, perLineStatus);
    }

    public static LineVerificationStatus[] RenderPerLineDiagnostics(
      DocumentUri uri,
      ICollection<VerificationTree> verificationTrees,
      int numberOfLines,
      bool verificationStarted,
      Container<Diagnostic> parseAndResolutionErrors) {
      var result = new LineVerificationStatus[numberOfLines];

      if (verificationTrees.Count == 0 && !parseAndResolutionErrors.Any() && verificationStarted) {
        for (var line = 0; line < numberOfLines; line++) {
          result[line] = LineVerificationStatus.Verified;
        }

        return result;
      }

      var oneMemberHasOnly =
        verificationTrees.Any(tree => tree is TopLevelDeclMemberVerificationTree { MarkedAsOnly: true });

      // Render verification tree content into lines.
      foreach (var verificationTree in verificationTrees) {
        if (verificationTree.Uri == uri) {
          if (oneMemberHasOnly && verificationTree is TopLevelDeclMemberVerificationTree { MarkedAsOnly: false }) {
            verificationTree.StatusCurrent = CurrentStatus.Current;
            verificationTree.StatusVerification = GutterVerificationStatus.Skipped;
          }
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


  public enum GutterVerificationStatus {
    Nothing = 0,
    Verified = 200,
    Skipped = 250,
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
    Skipped = 250,
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
  ///
  /// The difference between "Range" and "Position" is that "Range" contains two positions that include the entire tree,
  /// whereas "Position" is a single position that uniquely determines the range, e.g. a symbol position.
  /// That position typically serves as an placeholder to uniquely determine a method.
  ///  
  /// For example:
  /// 
  ///     method Test() {}
  ///     ^Range.Start   ^Range.End
  ///            ^ Position 
  /// </summary>
  /// <param name="DisplayName">A user-facing name of this node, to be displayed in an IDE explorer</param>
  /// <param name="Identifier">A unique identifier, to be used by the IDE to request re-verification</param>
  /// <param name="Filename">The name of the file this region of the document is contained in</param>
  /// <param name="Range">The range of this region of the document</param>
  /// <param name="Position">The position that uniquely identify this range</param>
  public record VerificationTree(
     // Method, Function, Subset type, Constant, Document, Assertion...
     string Kind,
     // User-facing short name
     string DisplayName,
     // Used to re-trigger the verification of some diagnostics.
     string Identifier,
     string Filename,
     Uri Uri,
     // The start and end of this verification tree
     Range Range,
     // The position of the symbol name attached to this node, or Range.Start if it's anonymous
     Position Position
  ) {
    public string PrefixedDisplayName => Kind + " `" + DisplayName + "`";

    // Overriden by checking children if there are some
    public GutterVerificationStatus StatusVerification { get; set; } = GutterVerificationStatus.Nothing;

    // Overriden by checking children if there are some
    public CurrentStatus StatusCurrent { get; set; } = CurrentStatus.Obsolete;

    /// Time and Resource diagnostics
    public bool Started { get; set; } = false;
    public bool Finished { get; set; } = false;
    public DateTime StartTime { get; protected set; }
    public DateTime EndTime { get; protected set; }
    public int TimeSpent => (int)(Finished ? ((TimeSpan)(EndTime - StartTime)).TotalMilliseconds : Started ? (DateTime.Now - StartTime).TotalMilliseconds : 0);
    // Resources allocated at the end of the computation.
    public long ResourceCount { get; set; } = 0;

    public List<TrackedNodeComponent> CoveredIds { get; set; } = [];

    // Sub-diagnostics if any
    public ConcurrentBag<VerificationTree> Children { get; set; } = [];
    public ConcurrentBag<VerificationTree> NewChildren { get; set; } = [];

    public void Visit(Action<VerificationTree> action) {
      action(this);
      foreach (var child in Children) {
        child.Visit(action);
      }
    }

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
      NewChildren = [];
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
        StartTime = DateTime.Now;
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
        EndTime = DateTime.Now;
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
        if (child.StatusVerification == GutterVerificationStatus.Error) {
          childrenHaveErrors = true;
        }
      }

      if (childrenHaveErrors) {
        StatusVerification = GutterVerificationStatus.Error;
      }
    }

    public static LineVerificationStatus RenderLineVerificationStatus(
      bool isFinalError, bool contextHasErrors, bool contextIsPending,
      CurrentStatus currentStatus, GutterVerificationStatus verificationStatus) {
      LineVerificationStatus simpleStatus = verificationStatus switch {
        GutterVerificationStatus.Skipped => LineVerificationStatus.Skipped, // Always current
        GutterVerificationStatus.Nothing => LineVerificationStatus.Nothing,
        // let's be careful to no display "Verified" for a range if the context does not have errors and is pending
        // because there might be other errors on the same range.
        GutterVerificationStatus.Verified =>
          contextHasErrors
            ? isFinalError // Sub-implementations that are verified do not count
              ? LineVerificationStatus.AssertionVerifiedInErrorContext
              : LineVerificationStatus.ErrorContext
            : contextIsPending && !isFinalError
              ? LineVerificationStatus.Nothing
              : LineVerificationStatus.Verified,
        // We don't display inconclusive on the gutter (user should focus on errors),
        // We display an error range instead
        GutterVerificationStatus.Inconclusive => isFinalError
          ? LineVerificationStatus.AssertionFailed
          : LineVerificationStatus.ErrorContext,
        GutterVerificationStatus.Error => isFinalError
            ? LineVerificationStatus.AssertionFailed
            : LineVerificationStatus.ErrorContext,
        _ => throw new ArgumentOutOfRangeException()
      };
      return
        simpleStatus == LineVerificationStatus.Skipped ? simpleStatus :
          (LineVerificationStatus)((int)simpleStatus + (int)currentStatus);
    }

    protected virtual bool IsFinalError => false;

    // Requires PropagateChildrenErrorsUp to have been called before.
    public virtual void RenderInto(LineVerificationStatus[] perLineDiagnostics, bool contextHasErrors = false, bool contextIsPending = false, Range? otherRange = null, Range? contextRange = null) {
      Range range = otherRange ?? Range;
      var isFinalError = range.Start.Line == range.End.Line || IsFinalError;
      LineVerificationStatus targetStatus = RenderLineVerificationStatus(isFinalError, contextHasErrors, contextIsPending, StatusCurrent, StatusVerification);
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
          contextHasErrors || StatusVerification == GutterVerificationStatus.Error,
          contextIsPending ||
            StatusCurrent == CurrentStatus.Obsolete ||
          StatusCurrent == CurrentStatus.Verifying,
          null,
          Range);
      }
      // Ensure that if this is an ImplementationVerificationTree, and children "painted" verified,
      // and this node is still pending
      // at least the first line should show pending.
      if (range.Start.Line >= 0 && range.End.Line < perLineDiagnostics.Length) {
        if (StatusCurrent == CurrentStatus.Verifying &&
            perLineDiagnostics.ToList().GetRange(range.Start.Line, range.End.Line - range.Start.Line + 1).All(
              line => line == LineVerificationStatus.Verified)) {
          perLineDiagnostics[range.Start.Line] = targetStatus;
        }
      }
    }

    public virtual VerificationTree GetCopyForNotification() {
      return this with {
        Children = new ConcurrentBag<VerificationTree>(Children.Select(child => child.GetCopyForNotification()))
      };
    }
  }

  public record DocumentVerificationTree(
    INode Program,
    Uri Uri)
    : VerificationTree("Document", Uri.ToString(), Uri.ToString(), Uri.ToString(), Uri, ComputeRange(Program, Uri), new Position(0, 0)) {

    private static Range ComputeRange(INode node, Uri uri) {
      if (node is not Program program) {
        return new Range(0, 0, -1, 0);
      }
      var end = program.Files.FirstOrDefault(f => f.Origin.Uri == uri)?.EndToken ?? Token.NoToken;
      while (end.Next != null) {
        end = end.Next;
      }

      var endPosition = end.GetLspPosition();
      var endTriviaLines = end.TrailingTrivia.Split("\n");
      endPosition = new Position(endPosition.Line + endTriviaLines.Length - 1,
        endPosition.Character + endTriviaLines[^1].Length);

      return new Range(new Position(0, 0), endPosition);
    }
  }

  public record TopLevelDeclMemberVerificationTree(
    string Kind,
    string DisplayName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    Uri Uri,
    // The range of this node.
    Range Range,
    Position Position,
    bool MarkedAsOnly
  ) : VerificationTree(Kind, DisplayName, Identifier, Filename, Uri, Range, Position) {
    // Recomputed from the children which are ImplementationVerificationTree
    public ImmutableDictionary<AssertionBatchIndex, AssertionBatchVerificationTree> AssertionBatches { get; private set; } =
      new Dictionary<AssertionBatchIndex, AssertionBatchVerificationTree>().ToImmutableDictionary();

    public override VerificationTree GetCopyForNotification() {
      return this with {
        Children = new ConcurrentBag<VerificationTree>(Children.Select(child => child.GetCopyForNotification())),
        AssertionBatches = AssertionBatches
          .Select(keyValuePair =>
            (keyValuePair.Key, (AssertionBatchVerificationTree)keyValuePair.Value.GetCopyForNotification()))
          .ToImmutableDictionary(keyValuePair => keyValuePair.Item1, KeyValuePair => KeyValuePair.Item2)
      };
    }

    public void RecomputeAssertionBatchNodeDiagnostics() {
      var result = new Dictionary<AssertionBatchIndex, AssertionBatchVerificationTree>();
      var implementationNumber = 0;
      foreach (var implementationNode in Children.OfType<ImplementationVerificationTree>()) {
        implementationNumber++;
        foreach (var vcNum in implementationNode.AssertionBatchMetrics.Keys.OrderBy(x => x)) {
          var children = new ConcurrentBag<VerificationTree>(implementationNode.Children.OfType<AssertionVerificationTree>().Where(
            assertionNode => assertionNode.AssertionBatchNum == vcNum));
          var minPosition = children.Count > 0 ? children.MinBy(child => child.Position)!.Range.Start : Range.Start;
          var maxPosition = children.Count > 0 ? children.MaxBy(child => child.Range.End)!.Range.End : Range.Start;
          result[new AssertionBatchIndex(implementationNumber, vcNum)] = new AssertionBatchVerificationTree(
            $"Assertion batch #{result.Count + 1}",
            implementationNode.VerboseName,
            $"assertion-batch-{implementationNumber}-{vcNum}",
            Filename,
            Uri,
            new Range(minPosition, maxPosition)
          ) {
            Children = children,
            ResourceCount = implementationNode.AssertionBatchMetrics[vcNum].ResourceCount,
            CoveredIds = implementationNode.AssertionBatchMetrics[vcNum].CoveredIds,
            RelativeNumber = result.Count + 1,
          }.WithDuration(implementationNode.StartTime, implementationNode.AssertionBatchMetrics[vcNum].Time);
        }
      }

      AssertionBatches = result.ToImmutableDictionary();
    }

    public AssertionBatchVerificationTree? GetCostlierAssertionBatch() =>
      !AssertionBatches.Any() ? null :
      AssertionBatches.Values.MaxBy(assertionBatch => assertionBatch.ResourceCount);

    public List<int> AssertionBatchTimes =>
      AssertionBatches.Values.Select(assertionBatch => assertionBatch.TimeSpent).ToList();

    // Currently the best estimate of the number of assertion batches
    public int AssertionBatchCount =>
      AssertionBatches.Keys.GroupBy(key => key.ImplementationIndex).Select(group =>
        group.Select(key => key.RelativeIndex).Max()).Sum();

    public int LongestAssertionBatchTime => AssertionBatches.Any() ? AssertionBatchTimes.Max() : 0;

    public int LongestAssertionBatchTimeIndex => LongestAssertionBatchTime != 0 ? AssertionBatchTimes.IndexOf(LongestAssertionBatchTime) : -1;
  }

  // Invariant: There is at least 1 child for every assertion batch
  public record AssertionBatchVerificationTree(
    string DisplayName,
    string VerboseName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    Uri Uri,
    // The range of this node.
    Range Range
  ) : VerificationTree("Assertion Batch", DisplayName, Identifier, Filename, Uri, Range, Range.Start) {
    public int NumberOfAssertions => Children.Count;

    public AssertionBatchVerificationTree WithDuration(DateTime parentStartTime, int implementationNodeAssertionBatchTime) {
      Started = true;
      Finished = true;
      StartTime = parentStartTime;
      EndTime = parentStartTime.AddMilliseconds(implementationNodeAssertionBatchTime);
      return this;
    }
    public override VerificationTree GetCopyForNotification() {
      return this with {
        Children = new ConcurrentBag<VerificationTree>(Children.Select(child => child.GetCopyForNotification()))
      };
    }

    public int RelativeNumber { get; init; }
  }

  public record AssertionBatchMetrics(
    int Time,
    int ResourceCount,
    List<TrackedNodeComponent> CoveredIds
  );

  public record ImplementationVerificationTree(
    string DisplayName,
    string VerboseName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    Uri Uri,
    // The range of this node.
    Range Range,
    // The position as used by Boogie
    Position Position
  ) : VerificationTree("Implementation", DisplayName, Identifier, Filename, Uri, Range, Position) {
    // The index of ImplementationVerificationTree.AssertionBatchTimes
    // is the same as the AssertionVerificationTree.AssertionBatchIndex
    public ImmutableDictionary<int, AssertionBatchMetrics> AssertionBatchMetrics { get; private set; } =
      new Dictionary<int, AssertionBatchMetrics>().ToImmutableDictionary();
    private Dictionary<int, AssertionBatchMetrics> NewAssertionBatchMetrics { get; set; } =
      new Dictionary<int, AssertionBatchMetrics>();

    public override VerificationTree GetCopyForNotification() {
      return this with {
        Children = new ConcurrentBag<VerificationTree>(Children.Select(child => child.GetCopyForNotification())),
        AssertionBatchMetrics = new Dictionary<int, AssertionBatchMetrics>(AssertionBatchMetrics).ToImmutableDictionary()
      };
    }

    private Implementation? implementation = null;

    public void AddAssertionBatchMetrics(int vcNum, int milliseconds, int resourceCount, List<TrackedNodeComponent> coveredIds) {
      NewAssertionBatchMetrics[vcNum] = new AssertionBatchMetrics(milliseconds, resourceCount, coveredIds);
    }

    public override bool Start() {
      if (base.Start()) {
        NewAssertionBatchMetrics = new Dictionary<int, AssertionBatchMetrics>();
        return true;
      }

      return false;
    }

    public override bool Stop() {
      if (base.Stop()) {
        AssertionBatchMetrics = NewAssertionBatchMetrics.ToImmutableDictionary();
        NewAssertionBatchMetrics = new Dictionary<int, AssertionBatchMetrics>();
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
  };

  public record AssertionVerificationTree(
    string DisplayName,
    // Used to re-trigger the verification of some diagnostics.
    string Identifier,
    string Filename,
    Uri Uri,
    // Used to relocate a assertion verification tree and to determine which function is currently verifying
    Position? SecondaryPosition,
    // The range of this node.
    Range Range
  ) : VerificationTree("Assertion", DisplayName, Identifier, Filename, Uri, Range, Range.Start) {
    public AssertionVerificationTree WithDuration(DateTime parentStartTime, int batchTime) {
      Started = true;
      Finished = true;
      StartTime = parentStartTime;
      EndTime = parentStartTime.AddMilliseconds(batchTime);
      return this;
    }

    protected override bool IsFinalError => true;

    // Ranges that should also display an error
    // TODO: Will need to compute this statically for the tests
    public List<Range> ImmediatelyRelatedRanges { get; set; } = [];
    public List<Range> DynamicallyRelatedRanges { get; set; } = [];

    /// <summary>
    /// Which assertion batch this assertion was taken from in its implementation node
    /// </summary>
    public int AssertionBatchNum { get; init; }

    public AssertionVerificationTree
      WithAssertionAndCounterExample(AssertCmd? inAssertion, Counterexample? inCounterExample) {
      this.assertion = inAssertion;
      this.counterExample = inCounterExample;
      return WithImmediatelyRelatedChanges().WithDynamicallyRelatedChanges();
    }

    private AssertionVerificationTree WithImmediatelyRelatedChanges() {
      if (assertion == null) {
        ImmediatelyRelatedRanges = [];
        return this;
      }

      var tok = assertion.tok;
      var result = new List<Range>();
      while (tok is NestedOrigin nestedToken) {
        tok = nestedToken.Inner;
        if (tok.filename == assertion.tok.filename) {
          result.Add(tok.GetLspRange());
        }
      }

      if (counterExample is ReturnCounterexample returnCounterexample) {
        tok = returnCounterexample.FailingReturn.tok;
        if (tok.filename == assertion.tok.filename) {
          result.Add(BoogieGenerator.ToDafnyToken(true, returnCounterexample.FailingReturn.tok).StartToken.GetLspRange());
        }
      }

      ImmediatelyRelatedRanges = result;
      return this;
    }

    private AssertionVerificationTree WithDynamicallyRelatedChanges() {
      // Ranges that should highlight when stepping on one error.
      if (assertion == null) {
        DynamicallyRelatedRanges = [];
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
      if (StatusVerification == GutterVerificationStatus.Error) {
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
  }

  public record AssertionBatchIndex(int ImplementationIndex, int RelativeIndex);
}
