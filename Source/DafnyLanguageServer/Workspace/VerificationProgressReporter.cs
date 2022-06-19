using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;
using VerificationResult = Microsoft.Boogie.VerificationResult;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class VerificationProgressReporter : IVerificationProgressReporter {
  /// The last [MaxLastTouchedMethods] recently modified methods will be
  /// automatically assigned a priority ranging from
  /// [MaxLastTouchedMethodPriority - MaxLastTouchedMethods + 1]
  /// to [MaxLastTouchedMethodPriority] (below, from 6 to 10)
  /// Since priorities range from 1 to infinite, the only requirement is
  /// that [MaxLastTouchedMethods] is less than [MaxLastTouchedMethodPriority]
  /// 10 is a nice priority, not too high so that it can be overriden easily
  /// to always trigger the verifier to verify them first (for any reason) 
  /// and not too low so that it's still possible to manually set up priorities 1-5 to
  /// methods that are not being modified.
  private const int MaxLastTouchedMethodPriority = 10;
  private const int MaxLastTouchedMethods = 5;

  private readonly ICompilationStatusNotificationPublisher statusPublisher;
  private readonly DafnyDocument document;
  private readonly ILogger<VerificationProgressReporter> logger;
  private readonly INotificationPublisher notificationPublisher;

  public VerificationProgressReporter(ILogger<VerificationProgressReporter> logger,
    DafnyDocument document,
    ICompilationStatusNotificationPublisher statusPublisher,
    INotificationPublisher notificationPublisher
  ) {
    this.document = document;
    this.statusPublisher = statusPublisher;
    this.logger = logger;
    this.notificationPublisher = notificationPublisher;
  }

  /// <summary>
  /// Sends a more precise verification status message to the client's status bar
  /// </summary>
  public void ReportProgress(string message) {
    statusPublisher.SendStatusNotification(document.TextDocumentItem, CompilationStatus.VerificationStarted, message);
  }

  /// <summary>
  /// Fills up the document with empty verification diagnostics, one for each top-level declarations
  /// Possibly migrates previous diagnostics
  /// </summary>
  public void RecomputeVerificationTree() {
    var previousTrees = document.VerificationTree.Children;

    List<VerificationTree> result = new List<VerificationTree>();

    HashSet<Position> recordedPositions = new HashSet<Position>();

    void AddAndPossiblyMigrateVerificationTree(VerificationTree verificationTree) {
      var position = verificationTree.Position;
      var previousTree = previousTrees.FirstOrDefault(
        oldNode => oldNode != null && oldNode.Position == position,
        null);
      if (previousTree != null) {
        previousTree.SetObsolete();
        verificationTree.StatusVerification = previousTree.StatusVerification;
        verificationTree.StatusCurrent = CurrentStatus.Obsolete;
        verificationTree.Children = previousTree.Children;
      }
      // Prevent duplicating trees, e.g. reveal lemmas that have the same position as the function. 
      if (!recordedPositions.Contains(verificationTree.Position)) {
        result.Add(verificationTree);
        recordedPositions.Add(verificationTree.Position);
      }
    }

    var documentFilePath = document.GetFilePath();
    foreach (var module in document.Program.Modules()) {
      foreach (var topLevelDecl in module.TopLevelDecls) {
        if (topLevelDecl is DatatypeDecl datatypeDecl) {
          foreach (DatatypeCtor ctor in datatypeDecl.Ctors) {
            var aFormalHasADefaultValue = ctor.Destructors.SelectMany(
              destructor => destructor.CorrespondingFormals).Any(
              formal => formal.DefaultValue != null);
            if (aFormalHasADefaultValue) {
              var verificationTreeRange = ctor.tok.GetLspRange(ctor.BodyEndTok);
              var verificationTree = new TopLevelDeclMemberVerificationTree(
                "datatype",
                ctor.Name,
                ctor.CompileName,
                ctor.tok.filename,
                verificationTreeRange);
              AddAndPossiblyMigrateVerificationTree(verificationTree);
            }
          }
        }
        if (topLevelDecl is TopLevelDeclWithMembers topLevelDeclWithMembers) {
          foreach (var member in topLevelDeclWithMembers.Members) {
            var memberWasNotIncluded = member.tok.filename != documentFilePath;
            if (memberWasNotIncluded) {
              continue;
            }
            if (member is Field) {
              var constantHasNoBody = member.BodyEndTok.line == 0;
              if (constantHasNoBody) {
                continue; // Nothing to verify
              }
              var verificationTreeRange = member.tok.GetLspRange(member.BodyEndTok);
              var verificationTree = new TopLevelDeclMemberVerificationTree(
                "constant",
                member.Name,
                member.CompileName,
                member.tok.filename,
                verificationTreeRange);
              AddAndPossiblyMigrateVerificationTree(verificationTree);
            } else if (member is Method or Function) {
              var verificationTreeRange = member.tok.GetLspRange(member.BodyEndTok.line == 0 ? member.tok : member.BodyEndTok);
              var verificationTree = new TopLevelDeclMemberVerificationTree(
                (member is Method ? "method" : "function"),
                member.Name,
                member.CompileName,
                member.tok.filename,
                verificationTreeRange);
              AddAndPossiblyMigrateVerificationTree(verificationTree);
              if (member is Function { ByMethodBody: { } } function) {
                var verificationTreeRangeByMethod = function.ByMethodTok.GetLspRange(function.ByMethodBody.EndTok);
                var verificationTreeByMethod = new TopLevelDeclMemberVerificationTree(
                  "by method part of function",
                  member.Name,
                  member.CompileName + "_by_method",
                  member.tok.filename,
                  verificationTreeRangeByMethod);
                AddAndPossiblyMigrateVerificationTree(verificationTreeByMethod);
              }
            }
          }
        }
        if (topLevelDecl is SubsetTypeDecl subsetTypeDecl) {
          if (subsetTypeDecl.tok.filename != documentFilePath) {
            continue;
          }
          var verificationTreeRange = subsetTypeDecl.tok.GetLspRange(subsetTypeDecl.BodyEndTok);
          var verificationTree = new TopLevelDeclMemberVerificationTree(
            $"subset type",
            subsetTypeDecl.Name,
            subsetTypeDecl.CompileName,
            subsetTypeDecl.tok.filename,
            verificationTreeRange);
          AddAndPossiblyMigrateVerificationTree(verificationTree);
        }
      }
    }
    document.VerificationTree.Children = result;
  }

  /// <summary>
  /// On receiving all implementations that are going to be verified, assign each implementation
  /// to its original method tree.
  /// Also set the implementation priority depending on the last edited methods 
  /// </summary>
  /// <param name="implementations">The implementations to be verified</param>
  public virtual void ReportImplementationsBeforeVerification(Implementation[] implementations) {
    if (document.LoadCanceled) {
      return;
    }
    var newLastTouchedMethodPositions = document.LastTouchedMethodPositions.ToList();
    var newlyTouchedVerificationTree = document.VerificationTree.Children.FirstOrDefault(node =>
      node != null && document.LastChange != null && node.Range.Contains(document.LastChange), null);
    if (newlyTouchedVerificationTree != null) {
      RememberLastTouchedMethodPositions(newlyTouchedVerificationTree.Position, newLastTouchedMethodPositions);
      document.LastTouchedMethodPositions = newLastTouchedMethodPositions.TakeLast(MaxLastTouchedMethods).ToImmutableList();
    }

    var positionToVerificationTree = document.VerificationTree.Children.ToImmutableDictionary(
      verificationTree => verificationTree.Position,
      verificationTree => verificationTree);

    // We migrate existing implementations to the new provided ones if they exist.
    // (same child number, same file and same position)
    foreach (var methodTree in document.VerificationTree.Children) {
      methodTree.ResetNewChildren();
    }

    foreach (var implementation in implementations) {
      var verificationTree = positionToVerificationTree!.GetValueOrDefault(implementation.tok.GetLspPosition(), null);
      int priority = GetVerificationPriority(verificationTree);

      if (priority > 0 && implementation.Priority < priority) {
        implementation.Attributes.AddLast(
          new QKeyValue(
            implementation.tok,
            "priority",
            new List<object>() {
              new Boogie.LiteralExpr(implementation.tok, BigNum.FromInt(priority))
            }, null));
      }

      var targetMethodNode = GetTargetMethodTree(implementation, out var oldImplementationNode, true);
      if (targetMethodNode == null) {
        var position = implementation.tok.GetLspPosition();
        var availableMethodNodes = string.Join(",", document.VerificationTree.Children.Select(vt =>
          $"{vt.Kind} {vt.DisplayName} at {vt.Filename}:{vt.Position.Line}"));
        logger.LogError($"In document {document.Uri} and filename {document.VerificationTree.Filename}, no method node at {implementation.tok.filename}:{position.Line}:{position.Character}.\nAvailable:" + availableMethodNodes);
        continue;
      }
      var newDisplayName = targetMethodNode.DisplayName + " #" + (targetMethodNode.Children.Count + 1) + ":" +
                           implementation.VerboseName;
      var newImplementationNode = new ImplementationVerificationTree(
        newDisplayName,
        implementation.VerboseName,
        targetMethodNode.Filename,
        targetMethodNode.Range
      ).WithImplementation(implementation);
      if (oldImplementationNode != null) {
        newImplementationNode.Children = oldImplementationNode.Children;
      }
      targetMethodNode?.AddNewChild(newImplementationNode);
    }

    foreach (var methodNode in document.VerificationTree.Children.OfType<TopLevelDeclMemberVerificationTree>()) {
      methodNode.SaveNewChildren();
      if (!methodNode.Children.Any()) {
        methodNode.Start();
        methodNode.Stop();
        methodNode.StatusCurrent = CurrentStatus.Current;
        methodNode.StatusVerification = GutterVerificationStatus.Verified;
      }
      methodNode.PropagateChildrenErrorsUp();
      methodNode.RecomputeAssertionBatchNodeDiagnostics();
    }
  }

  /// <summary>
  /// Triggers sending of the current verification diagnostics to the client
  /// </summary>
  /// <param name="verificationStarted">Whether verification already started at this point</param>
  /// <param name="dafnyDocument">The document to send. Can be a previous document</param>
  public void ReportRealtimeDiagnostics(bool verificationStarted, DafnyDocument? dafnyDocument = null) {
    lock (LockProcessing) {
      dafnyDocument ??= document;
      if (dafnyDocument.LoadCanceled) {
        return;
      }
      notificationPublisher.PublishGutterIcons(document, verificationStarted);
    }
  }

  // TODO for backwards compatibility. No longer needed when the IDE switches to the textDocument/verificationStatus API
  /// <summary>
  /// Helper to send a more precise verification status message, including
  /// - The number of methods already verified
  /// - The total number of methods
  /// - The methods being currently verified
  /// - Some extra information 
  /// </summary>
  /// <param name="extra">Usually the name of the method whose check was just finished, if any</param>
  private void ReportMethodsBeingVerified(string extra = "") {
    var pending = document.VerificationTree.Children
      .Where(diagnostic => diagnostic.Started && !diagnostic.Finished)
      .OrderBy(diagnostic => diagnostic.StartTime)
      .Select(diagnostic => diagnostic.DisplayName)
      .ToList();
    var total = document.VerificationTree.Children.Count;
    var verified = document.VerificationTree.Children.Count(diagnostic => diagnostic.Finished);
    var message = string.Join(", ", pending) + (!pending.Any() ? extra.Trim() : extra);
    ReportProgress($"{verified}/{total} {message}");
  }

  /// <summary>
  /// Called when the verifier starts verifying an implementation
  /// </summary>
  /// <param name="implementation">The implementation which is going to be verified next</param>
  public void ReportStartVerifyImplementation(Implementation implementation) {
    if (document.LoadCanceled) {
      return;
    }

    lock (LockProcessing) {
      var targetMethodNode = GetTargetMethodTree(implementation, out var implementationNode);
      if (targetMethodNode == null) {
        logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
      } else {
        if (!targetMethodNode.Started) {
          // The same method could be started multiple times for each implementation
          targetMethodNode.Start();
          ReportMethodsBeingVerified();
        }

        if (implementationNode == null) {
          logger.LogError($"No implementation at {implementation.tok}");
        } else {
          implementationNode.Start();
        }

        targetMethodNode.PropagateChildrenErrorsUp();
        ReportRealtimeDiagnostics(true);
      }
    }
  }

  /// <summary>
  /// Called when the verifier finished to visit an implementation
  /// </summary>
  /// <param name="implementation">The implementation it visited</param>
  /// <param name="verificationResult">The result of the verification</param>
  public void ReportEndVerifyImplementation(Implementation implementation, VerificationResult verificationResult) {
    if (document.LoadCanceled) {
      return;
    }
    var targetMethodNode = GetTargetMethodTree(implementation, out var implementationNode);
    if (targetMethodNode == null) {
      logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
    } else if (implementationNode == null) {
      logger.LogError($"No implementation node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
    } else {
      lock (LockProcessing) {
        implementationNode.Stop();
        implementationNode.ResourceCount = verificationResult.ResourceCount;
        targetMethodNode.ResourceCount += verificationResult.ResourceCount;
        var finalOutcome = verificationResult.Outcome switch {
          ConditionGeneration.Outcome.Correct => GutterVerificationStatus.Verified,
          _ => GutterVerificationStatus.Error
        };

        implementationNode.StatusVerification = finalOutcome;
        // Will be only executed by the last instance.
        if (!targetMethodNode.Children.All(child => child.Finished)) {
          targetMethodNode.StatusVerification = verificationResult.Outcome switch {
            ConditionGeneration.Outcome.Correct => targetMethodNode.StatusVerification,
            _ => GutterVerificationStatus.Error
          };
        } else {
          targetMethodNode.Stop();
          ReportMethodsBeingVerified($" ({targetMethodNode.DisplayName} finished)");
          // Later, will be overriden by individual outcomes
          targetMethodNode.StatusVerification = finalOutcome;
        }

        targetMethodNode.PropagateChildrenErrorsUp();
        targetMethodNode.RecomputeAssertionBatchNodeDiagnostics();
        ReportRealtimeDiagnostics(true);
      }
    }
  }

  /// <summary>
  /// Called when a split is finished to be verified
  /// </summary>
  /// <param name="split">The split that was verified</param>
  /// <param name="result">The verification results for that split and per assert</param>
  public void ReportAssertionBatchResult(AssertionBatchResult batchResult) {
    if (document.LoadCanceled) {
      return;
    }
    lock (LockProcessing) {
      var split = batchResult.Split;
      var result = batchResult.Result;
      var implementation = split.Implementation;
      // While there is no error, just add successful nodes.
      var targetMethodNode = GetTargetMethodTree(implementation, out var implementationNode);
      if (targetMethodNode == null) {
        logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
      } else if (implementationNode == null) {
        logger.LogError($"No implementation node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
      } else {
        result.ComputePerAssertOutcomes(out var perAssertOutcome, out var perAssertCounterExample);

        var assertionBatchTime = (int)result.runTime.TotalMilliseconds;
        var assertionBatchResourceCount = result.resourceCount;
        implementationNode.AddAssertionBatchMetrics(result.vcNum, assertionBatchTime, assertionBatchResourceCount);

        // Attaches the trace
        void AddChildOutcome(Counterexample? counterexample, AssertCmd assertCmd, IToken token,
          GutterVerificationStatus status, IToken? secondaryToken, string? assertDisplay = "",
          string assertIdentifier = "") {
          if (token.filename != implementationNode.Filename) {
            return;
          }

          var outcomePosition = token.GetLspPosition();
          var secondaryOutcomePosition = secondaryToken?.GetLspPosition();

          var childrenCount = implementationNode.GetNewChildrenCount();
          assertDisplay = assertDisplay != "" ? " " + assertDisplay : "";
          assertIdentifier = assertIdentifier != "" ? "_" + assertIdentifier : "";

          var outcomeRange = token.GetLspRange();
          var nodeDiagnostic = new AssertionVerificationTree(
            $"{targetMethodNode.DisplayName}{assertDisplay} #{childrenCount}",
            $"{targetMethodNode.Identifier}_{childrenCount}{assertIdentifier}",
            token.filename,
            secondaryOutcomePosition,
            outcomeRange
          ) {
            StatusVerification = status,
            StatusCurrent = CurrentStatus.Current,
            AssertionBatchNum = result.vcNum,
            Started = true,
            Finished = true
          }.WithDuration(implementationNode.StartTime, assertionBatchTime)
            .WithAssertionAndCounterExample(assertCmd, counterexample);
          // Add this diagnostics as the new one to display once the implementation is fully verified
          implementationNode.AddNewChild(nodeDiagnostic);
          // Update any previous pending "verifying" diagnostic as well so that they are updated in real-time
          var previousChild = implementationNode.Children.OfType<AssertionVerificationTree>()
            .FirstOrDefault(child =>
              child != null && child.Position == outcomePosition && (
                secondaryOutcomePosition == child.SecondaryPosition), null);
          if (previousChild != null) {
            // Temporary update of children.
            implementationNode.Children.Remove(previousChild);
            implementationNode.Children.Add(previousChild with {
              StatusCurrent = CurrentStatus.Current,
              StatusVerification = status
            });
          } else {
            implementationNode.Children.Add(nodeDiagnostic);
          }
        }

        foreach (var (assertCmd, outcome) in perAssertOutcome) {
          var status = GetNodeStatus(outcome);
          perAssertCounterExample.TryGetValue(assertCmd, out var counterexample);
          IToken? secondaryToken = counterexample is ReturnCounterexample returnCounterexample ? returnCounterexample.FailingReturn.tok :
            counterexample is CallCounterexample callCounterexample ? callCounterexample.FailingRequires.tok :
            null;
          if (assertCmd is AssertEnsuresCmd assertEnsuresCmd) {
            AddChildOutcome(counterexample, assertCmd, assertEnsuresCmd.Ensures.tok, status, secondaryToken, " ensures", "_ensures");
          } else if (assertCmd is AssertRequiresCmd assertRequiresCmd) {
            AddChildOutcome(counterexample, assertCmd, assertRequiresCmd.Call.tok, status, secondaryToken, assertDisplay: "Call", assertIdentifier: "call");
          } else {
            AddChildOutcome(counterexample, assertCmd, assertCmd.tok, status, secondaryToken, assertDisplay: "Assertion", assertIdentifier: "assert");
          }
        }
        targetMethodNode.PropagateChildrenErrorsUp();
        targetMethodNode.RecomputeAssertionBatchNodeDiagnostics();
        ReportRealtimeDiagnostics(true);
      }
    }
  }

  /// <summary>
  /// Returns the verification priority for a given method, depending on if it was recently modified
  /// </summary>
  /// <param name="method">The method to consider</param>
  /// <returns>The automatically set priority for the underlying method, or 0</returns>
  private int GetVerificationPriority(VerificationTree? method) {
    if (method != null) {
      var lastTouchedIndex = document.LastTouchedMethodPositions.IndexOf(method.Position);
      // 0 if not found
      if (lastTouchedIndex == -1) {
        return 0;
      }
      var lastTouchedCount = document.LastTouchedMethodPositions.Count;
      var priority = MaxLastTouchedMethodPriority + lastTouchedIndex + 1 - lastTouchedCount;
      return priority;
    }
    return 0;
  }

  /// <summary>
  /// Helper to remember that a method tree was recently modified.
  /// </summary>
  /// <param name="methodPosition">The verification tree of the method that was recently modified</param>
  /// <param name="newLastTouchedMethodPositions">The positions of recently touched methods</param>
  private void RememberLastTouchedMethodPositions(Position methodPosition, List<Position> newLastTouchedMethodPositions) {
    var index = newLastTouchedMethodPositions.IndexOf(methodPosition);
    if (index != -1) {
      newLastTouchedMethodPositions.RemoveAt(index);
    }
    newLastTouchedMethodPositions.Add(methodPosition);
  }

  /// <summary>
  /// Given an implementation, returns the top-level verification tree.
  /// </summary>
  /// <param name="implementation">The implementation</param>
  /// <param name="implementationTree">Returns the tree of the implementation child of the returned top-level verification tree</param>
  /// <param name="nameBased">Whether it should try to locate the implementation using the name rather than the position. Used to relocate previous diagnostics.</param>
  /// <returns>The top-level verification tree</returns>
  private TopLevelDeclMemberVerificationTree? GetTargetMethodTree(Implementation implementation, out ImplementationVerificationTree? implementationTree, bool nameBased = false) {
    var targetMethodNode = document.VerificationTree.Children.OfType<TopLevelDeclMemberVerificationTree>().FirstOrDefault(
      node => node?.Position == implementation.tok.GetLspPosition() && node?.Filename == implementation.tok.filename
      , null);
    if (nameBased) {
      implementationTree = targetMethodNode?.Children.OfType<ImplementationVerificationTree>().FirstOrDefault(
        node => {
          var nodeImpl = node?.GetImplementation();
          return nodeImpl?.Name == implementation.VerboseName;
        }, null);
    } else {
      implementationTree = targetMethodNode?.Children.OfType<ImplementationVerificationTree>().FirstOrDefault(
        node => node?.GetImplementation() == implementation, null);
    }

    return targetMethodNode;
  }

  /// <summary>
  /// An object to lock so that the updating of the verification trees is always not concurrent
  /// </summary>
  private readonly object LockProcessing = new();

  /// <summary>
  /// Converts a ProverInterface.Outcome to a VerificationStatus
  /// </summary>
  /// <param name="outcome">The outcome set by the split result</param>
  /// <returns>The matching verification status</returns>
  private static GutterVerificationStatus GetNodeStatus(ProverInterface.Outcome outcome) {
    return outcome switch {
      ProverInterface.Outcome.Valid => GutterVerificationStatus.Verified,
      ProverInterface.Outcome.Invalid => GutterVerificationStatus.Error,
      ProverInterface.Outcome.Undetermined => GutterVerificationStatus.Inconclusive,
      ProverInterface.Outcome.TimeOut => GutterVerificationStatus.Error,
      ProverInterface.Outcome.OutOfMemory => GutterVerificationStatus.Error,
      ProverInterface.Outcome.OutOfResource => GutterVerificationStatus.Error,
      ProverInterface.Outcome.Bounded => GutterVerificationStatus.Error,
      _ => GutterVerificationStatus.Error
    };
  }
}