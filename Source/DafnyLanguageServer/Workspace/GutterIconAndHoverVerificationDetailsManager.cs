using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;
using VerificationResult = Microsoft.Boogie.VerificationResult;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class GutterIconAndHoverVerificationDetailsManager : IGutterIconAndHoverVerificationDetailsManager {

  public static readonly Option<bool> LineVerificationStatus = new("--notify-line-verification-status", @"
(experimental, API will change)
Send notifications about the verification status of each line in the program.
".TrimStart());

  private readonly DafnyOptions options;
  private readonly ILogger<GutterIconAndHoverVerificationDetailsManager> logger;
  private readonly INotificationPublisher notificationPublisher;

  public GutterIconAndHoverVerificationDetailsManager(ILogger<GutterIconAndHoverVerificationDetailsManager> logger,
    INotificationPublisher notificationPublisher, DafnyOptions options) {
    this.logger = logger;
    this.notificationPublisher = notificationPublisher;
    this.options = options;
  }

  /// <summary>
  /// Fills up the document with empty verification diagnostics, one for each top-level declarations
  /// Possibly migrates previous diagnostics
  /// </summary>
  public void RecomputeVerificationTrees(CompilationAfterParsing compilation) {
    foreach (var uri in compilation.VerificationTrees.Keys) {
      compilation.VerificationTrees[uri] = UpdateTree(compilation.Program.Reporter.Options, compilation, compilation.VerificationTrees[uri]);
    }
  }

  private static DocumentVerificationTree UpdateTree(DafnyOptions options, CompilationAfterParsing parsedCompilation, DocumentVerificationTree rootVerificationTree) {
    var previousTrees = rootVerificationTree.Children;

    if (parsedCompilation is not CompilationAfterResolution) {
      return new DocumentVerificationTree(parsedCompilation.Program, rootVerificationTree.Uri) {
        Children = rootVerificationTree.Children
      };
    }

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

    foreach (var module in parsedCompilation.Program.Modules()) {
      foreach (var topLevelDecl in module.TopLevelDecls) {
        if (topLevelDecl is DatatypeDecl datatypeDecl) {
          foreach (DatatypeCtor ctor in datatypeDecl.Ctors) {
            var aFormalHasADefaultValue = ctor.Destructors.SelectMany(
              destructor => destructor.CorrespondingFormals).Any(
              formal => formal.DefaultValue != null);
            if (aFormalHasADefaultValue) {
              var verificationTreeRange = ctor.StartToken.GetLspRange(ctor.EndToken);
              var verificationTree = new TopLevelDeclMemberVerificationTree(
                "datatype",
                ctor.Name,
                ctor.GetCompileName(options),
                ctor.tok.Filepath,
                ctor.Tok.Uri,
                verificationTreeRange,
                ctor.tok.GetLspPosition(),
                Attributes.Contains(ctor.Attributes, "only")
                );
              AddAndPossiblyMigrateVerificationTree(verificationTree);
            }
          }
        }

        if (topLevelDecl is TopLevelDeclWithMembers topLevelDeclWithMembers) {
          foreach (var member in topLevelDeclWithMembers.Members) {
            var memberWasNotIncluded = member.tok.Uri != rootVerificationTree.Uri;
            if (memberWasNotIncluded) {
              continue;
            }

            if (member is ConstantField) {
              var constantHasNoBody = member.RangeToken.EndToken.line == 0;
              if (constantHasNoBody) {
                continue; // Nothing to verify
              }

              var verificationTreeRange = member.StartToken.GetLspRange(member.EndToken);
              var verificationTree = new TopLevelDeclMemberVerificationTree(
                "constant",
                member.Name,
                member.GetCompileName(options),
                member.tok.Filepath,
                member.Tok.Uri,
                verificationTreeRange,
                member.tok.GetLspPosition(),
                Attributes.Contains(member.Attributes, "only"));
              AddAndPossiblyMigrateVerificationTree(verificationTree);
            } else if (member is Method or Function) {
              var verificationTreeRange = member.StartToken.GetLspRange(member.EndToken);
              var verificationTree = new TopLevelDeclMemberVerificationTree(
                (member is Method ? "method" : "function"),
                member.Name,
                member.GetCompileName(options),
                member.tok.Filepath,
                member.Tok.Uri,
                verificationTreeRange,
                member.tok.GetLspPosition(),
                Attributes.Contains(member.Attributes, "only"));
              AddAndPossiblyMigrateVerificationTree(verificationTree);
              if (member is Function { ByMethodBody: { } } function) {
                var verificationTreeRangeByMethod = function.ByMethodBody.RangeToken.ToLspRange();
                var verificationTreeByMethod = new TopLevelDeclMemberVerificationTree(
                  "by method part of function",
                  member.Name,
                  member.GetCompileName(options) + "_by_method",
                  member.tok.Filepath,
                  member.Tok.Uri,
                  verificationTreeRangeByMethod,
                  function.ByMethodTok.GetLspPosition(),
                  Attributes.Contains(member.Attributes, "only"));
                AddAndPossiblyMigrateVerificationTree(verificationTreeByMethod);
              }
            }
          }
        }

        if (topLevelDecl is SubsetTypeDecl subsetTypeDecl) {
          if (subsetTypeDecl.tok.Uri != rootVerificationTree.Uri) {
            continue;
          }

          var verificationTreeRange = subsetTypeDecl.StartToken.GetLspRange(subsetTypeDecl.EndToken);
          var verificationTree = new TopLevelDeclMemberVerificationTree(
            $"subset type",
            subsetTypeDecl.Name,
            subsetTypeDecl.GetCompileName(options),
            subsetTypeDecl.tok.Filepath,
            subsetTypeDecl.Tok.Uri,
            verificationTreeRange,
            subsetTypeDecl.tok.GetLspPosition(),
            Attributes.Contains(subsetTypeDecl.Attributes, "only"));
          AddAndPossiblyMigrateVerificationTree(verificationTree);
        }
      }
    }

    return new DocumentVerificationTree(parsedCompilation.Program, rootVerificationTree.Uri) {
      Children = result
    };
  }

  /// <summary>
  /// On receiving all implementations that are going to be verified, assign each implementation
  /// to its original method tree.
  /// Also set the implementation priority depending on the last edited methods 
  /// </summary>
  public virtual void ReportImplementationsBeforeVerification(CompilationAfterResolution compilation, ICanVerify canVerify, Implementation[] implementations) {
    var uri = canVerify.Tok.Uri;
    var tree = compilation.VerificationTrees[uri];

    if (logger.IsEnabled(LogLevel.Debug)) {
      logger.LogDebug($"ReportImplementationsBeforeVerification for ${compilation.Project.Uri}, version {compilation.Version}, implementations: " +
                      $"{string.Join(", ", implementations.Select(i => i.Name))}");
    }

    // We migrate existing implementations to the new provided ones if they exist.
    // (same child number, same file and same position)
    var canVerifyNode = tree.Children.OfType<TopLevelDeclMemberVerificationTree>()
      .FirstOrDefault(t => t.Position == canVerify.Tok.GetLspPosition());
    if (canVerifyNode == null) {
      return;
    }


    canVerifyNode.ResetNewChildren();

    TopLevelDeclMemberVerificationTree? targetMethodNode;
    ImplementationVerificationTree newImplementationNode;
    foreach (var implementation in implementations) {

      targetMethodNode = GetTargetMethodTree(tree, implementation, out var oldImplementationNode, true);
      if (targetMethodNode == null) {
        NoMethodNodeAtLogging(tree, "ReportImplementationsBeforeVerification", compilation, implementation);
        continue;
      }

      var newDisplayName = targetMethodNode.DisplayName + " #" + (targetMethodNode.Children.Count + 1) + ":" +
                           implementation.Name;
      newImplementationNode = new ImplementationVerificationTree(
        newDisplayName,
        implementation.VerboseName,
        implementation.Name,
        targetMethodNode.Filename,
        targetMethodNode.Uri,
        targetMethodNode.Range,
        targetMethodNode.Position
      ).WithImplementation(implementation);
      if (oldImplementationNode != null) {
        newImplementationNode.Children = oldImplementationNode.Children;
      }

      targetMethodNode.AddNewChild(newImplementationNode);
    }

    var newChildren = canVerifyNode.NewChildren;
    canVerifyNode.SaveNewChildren();
    if (!canVerifyNode.Children.Any()) {
      canVerifyNode.Start();
      canVerifyNode.Stop();
      canVerifyNode.StatusCurrent = CurrentStatus.Current;
      canVerifyNode.StatusVerification = GutterVerificationStatus.Verified;
    }

    canVerifyNode.PropagateChildrenErrorsUp();
    canVerifyNode.RecomputeAssertionBatchNodeDiagnostics();
  }

  /// <summary>
  /// Triggers sending of the current verification diagnostics to the client
  /// </summary>
  public void PublishGutterIcons(CompilationAfterParsing compilation, Uri uri, bool verificationStarted) {
    if (options.Get(LineVerificationStatus)) {
      lock (LockProcessing) {
        notificationPublisher.PublishGutterIcons(uri, compilation.InitialIdeState(compilation, compilation.Program.Reporter.Options), verificationStarted);
      }
    }
  }

  /// <summary>
  /// Called when the verifier starts verifying an implementation
  /// </summary>
  public void ReportVerifyImplementationRunning(CompilationAfterResolution compilation, Implementation implementation) {
    var uri = ((IToken)implementation.tok).Uri;
    var tree = compilation.VerificationTrees[uri];

    lock (LockProcessing) {
      var targetMethodNode = GetTargetMethodTree(tree, implementation, out var implementationNode);
      if (targetMethodNode == null) {
        NoMethodNodeAtLogging(tree, "ReportVerifyImplementationRunning", compilation, implementation);
      } else {
        if (!targetMethodNode.Started) {
          // The same method could be started multiple times for each implementation
          targetMethodNode.Start();
        }

        if (implementationNode == null) {
          logger.LogError($"No implementation at {implementation.tok}");
        } else {
          implementationNode.Start();
        }

        targetMethodNode.PropagateChildrenErrorsUp();
        PublishGutterIcons(compilation, uri, true);
      }
    }
  }

  /// <summary>
  /// Called when the verifier finished to visit an implementation
  /// </summary>
  public void ReportEndVerifyImplementation(CompilationAfterResolution compilation, Implementation implementation, VerificationResult verificationResult) {

    var uri = ((IToken)implementation.tok).Uri;
    var tree = compilation.VerificationTrees[uri];

    var targetMethodNode = GetTargetMethodTree(tree, implementation, out var implementationNode);
    if (targetMethodNode == null) {
      NoMethodNodeAtLogging(tree, "ReportEndVerifyImplementation", compilation, implementation);
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
          // Later, will be overriden by individual outcomes
          targetMethodNode.StatusVerification = finalOutcome;
        }

        targetMethodNode.PropagateChildrenErrorsUp();
        targetMethodNode.RecomputeAssertionBatchNodeDiagnostics();
        PublishGutterIcons(compilation, uri, true);
      }
    }
  }

  private void NoMethodNodeAtLogging(VerificationTree tree, string methodName, CompilationAfterResolution compilation, Implementation implementation) {
    var position = implementation.tok.GetLspPosition();
    var availableMethodNodes = string.Join(",", tree!.Children.Select(vt =>
      $"{vt.Kind} {vt.DisplayName} at {vt.Filename}:{vt.Position.Line}"));
    logger.LogDebug(
      $"No method found in {methodName}, in document {compilation.Uri} and filename {tree.Filename}, " +
      $"no method node at {implementation.tok.filename}:{position.Line}:{position.Character}.\n" +
      $"Available nodes: " + availableMethodNodes);
  }

  /// <summary>
  /// Called when a split is finished to be verified
  /// </summary>
  public void ReportAssertionBatchResult(CompilationAfterResolution compilation, AssertionBatchResult batchResult) {
    var uri = ((IToken)batchResult.Implementation.tok).Uri;
    var tree = compilation.VerificationTrees[uri];

    lock (LockProcessing) {
      var implementation = batchResult.Implementation;
      var result = batchResult.Result;
      // While there is no error, just add successful nodes.
      var targetMethodNode = GetTargetMethodTree(tree, implementation, out var implementationNode);
      if (targetMethodNode == null) {
        NoMethodNodeAtLogging(tree, "ReportAssertionBatchResult", compilation, implementation);
      } else if (implementationNode == null) {
        logger.LogError($"No implementation node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
      } else {
        var wasAlreadyProcessed = implementationNode.NewChildren.Any(assertNode =>
          assertNode is AssertionVerificationTree assertionNode
          && assertionNode.AssertionBatchNum == result.vcNum);
        if (wasAlreadyProcessed) {
          return;
        }

        result.ComputePerAssertOutcomes(out var perAssertOutcome, out var perAssertCounterExample);

        var assertionBatchTime = (int)result.runTime.TotalMilliseconds;
        var assertionBatchResourceCount = result.resourceCount;
        implementationNode.AddAssertionBatchMetrics(result.vcNum, assertionBatchTime, assertionBatchResourceCount, result.coveredElements.ToList());

        // Attaches the trace
        void AddChildOutcome(Counterexample? counterexample, AssertCmd assertCmd, IToken token,
          GutterVerificationStatus status, IToken? secondaryToken, string? assertDisplay = "",
          string assertIdentifier = "") {
          if (token.Filepath != implementationNode.Filename) {
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
            token.Filepath,
            token.Uri,
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
          IToken? secondaryToken = BoogieGenerator.ToDafnyToken(counterexample is ReturnCounterexample returnCounterexample ? returnCounterexample.FailingReturn.tok :
            counterexample is CallCounterexample callCounterexample ? callCounterexample.FailingRequires.tok :
            null);
          if (assertCmd is AssertEnsuresCmd assertEnsuresCmd) {
            AddChildOutcome(counterexample, assertCmd, BoogieGenerator.ToDafnyToken(assertEnsuresCmd.Ensures.tok), status, secondaryToken, " ensures", "_ensures");
          } else if (assertCmd is AssertRequiresCmd assertRequiresCmd) {
            AddChildOutcome(counterexample, assertCmd, BoogieGenerator.ToDafnyToken(assertRequiresCmd.Call.tok), status, secondaryToken, assertDisplay: "Call", assertIdentifier: "call");
          } else {
            AddChildOutcome(counterexample, assertCmd, BoogieGenerator.ToDafnyToken(assertCmd.tok), status, secondaryToken, assertDisplay: "Assertion", assertIdentifier: "assert");
          }
        }
        targetMethodNode.PropagateChildrenErrorsUp();
        targetMethodNode.RecomputeAssertionBatchNodeDiagnostics();
        PublishGutterIcons(compilation, uri, true);
      }
    }
  }

  public void SetAllUnvisitedMethodsAsVerified(CompilationAfterResolution compilation, ICanVerify canVerify) {
    var tree = compilation.VerificationTrees[canVerify.Tok.Uri];
    var verifyTree = tree.Children.First(f => f.Position == canVerify.Tok.GetLspPosition());
    verifyTree.SetVerifiedIfPending();
  }


  /// <summary>
  /// Given an implementation, returns the top-level verification tree.
  /// </summary>
  /// <param name="implementation">The implementation</param>
  /// <param name="implementationTree">Returns the tree of the implementation child of the returned top-level verification tree</param>
  /// <param name="nameBased">Whether it should try to locate the implementation using the name rather than the position. Used to relocate previous diagnostics.</param>
  /// <returns>The top-level verification tree</returns>
  private TopLevelDeclMemberVerificationTree? GetTargetMethodTree(VerificationTree tree,
    Implementation implementation, out ImplementationVerificationTree? implementationTree, bool nameBased = false) {
    var targetMethodNode = tree.Children.OfType<TopLevelDeclMemberVerificationTree>().FirstOrDefault(
      node => node?.Position == implementation.tok.GetLspPosition() &&
              node?.Uri == ((IToken)implementation.tok).Uri
      , null);
    if (nameBased) {
      implementationTree = targetMethodNode?.Children.OfType<ImplementationVerificationTree>().FirstOrDefault(
        node => {
          var nodeImpl = node?.GetImplementation();
          return nodeImpl?.Name == implementation.Name;
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
