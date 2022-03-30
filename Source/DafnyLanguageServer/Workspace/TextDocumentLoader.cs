using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.BaseTypes;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using VC;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;
using VerificationResult = Microsoft.Boogie.VerificationResult;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Text document loader implementation that offloads the whole load procedure on one dedicated
  /// thread with a stack size of 256MB. Since only one thread is used, document loading is implicitely synchronized.
  /// The verification runs on the calling thread.
  /// </summary>
  /// <remarks>
  /// The increased stack size is necessary to solve the issue https://github.com/dafny-lang/dafny/issues/1447.
  /// </remarks>
  public class TextDocumentLoader : ITextDocumentLoader {
    // 256MB
    private const int MaxStackSize = 0x10000000;

    private readonly IDafnyParser parser;
    private readonly ISymbolResolver symbolResolver;
    private readonly ISymbolTableFactory symbolTableFactory;
    private readonly IProgramVerifier verifier;
    private readonly IGhostStateDiagnosticCollector ghostStateDiagnosticCollector;
    private readonly ICompilationStatusNotificationPublisher notificationPublisher;
    private readonly ILoggerFactory loggerFactory;
    private readonly ILogger<TextDocumentLoader> logger;
    private readonly IDiagnosticPublisher diagnosticPublisher;

    private TextDocumentLoader(
      ILoggerFactory loggerFactory,
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher notificationPublisher,
      IDiagnosticPublisher diagnosticPublisher) {
      this.parser = parser;
      this.symbolResolver = symbolResolver;
      this.verifier = verifier;
      this.symbolTableFactory = symbolTableFactory;
      this.ghostStateDiagnosticCollector = ghostStateDiagnosticCollector;
      this.notificationPublisher = notificationPublisher;
      this.loggerFactory = loggerFactory;
      this.logger = loggerFactory.CreateLogger<TextDocumentLoader>();
      this.diagnosticPublisher = diagnosticPublisher;
    }

    static readonly ThreadTaskScheduler LargeStackScheduler = new(MaxStackSize);

    public static TextDocumentLoader Create(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher notificationPublisher,
      ILoggerFactory loggerFactory,
      IDiagnosticPublisher diagnosticPublisher
      ) {
      return new TextDocumentLoader(loggerFactory, parser, symbolResolver, verifier, symbolTableFactory, ghostStateDiagnosticCollector, notificationPublisher, diagnosticPublisher);
    }

    public DafnyDocument CreateUnloaded(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var errorReporter = new DiagnosticErrorReporter(textDocument.Uri);
      return CreateDocumentWithEmptySymbolTable(
        loggerFactory.CreateLogger<SymbolTable>(),
        textDocument,
        errorReporter,
        parser.CreateUnparsed(textDocument, errorReporter, cancellationToken),
        loadCanceled: true
      );
    }

    public Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
#pragma warning disable CS1998
      // By using `async`, any OperationCancelledExceptions are converted to a cancelled Task.
      return Task.Factory.StartNew(async () => LoadInternal(textDocument, cancellationToken), cancellationToken,
        TaskCreationOptions.None, LargeStackScheduler).Unwrap();
#pragma warning restore CS1998
    }

    private DafnyDocument LoadInternal(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var errorReporter = new DiagnosticErrorReporter(textDocument.Uri);
      var program = parser.Parse(textDocument, errorReporter, cancellationToken);
      PublishDafnyLanguageServerLoadErrors(errorReporter, program);
      if (errorReporter.HasErrors) {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.ParsingFailed);
        return CreateDocumentWithEmptySymbolTable(loggerFactory.CreateLogger<SymbolTable>(), textDocument, errorReporter, program, loadCanceled: false);
      }

      var compilationUnit = symbolResolver.ResolveSymbols(textDocument, program, cancellationToken);
      var symbolTable = symbolTableFactory.CreateFrom(program, compilationUnit, cancellationToken);
      if (errorReporter.HasErrors) {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.ResolutionFailed);
      } else {
        notificationPublisher.SendStatusNotification(textDocument, CompilationStatus.CompilationSucceeded);
      }
      var ghostDiagnostics = ghostStateDiagnosticCollector.GetGhostStateDiagnostics(symbolTable, cancellationToken).ToArray();
      return new DafnyDocument(textDocument, errorReporter, new List<Diagnostic>(), ghostDiagnostics, program, symbolTable) {
        ResolutionSucceeded = !errorReporter.HasErrors
      };
    }

    private static void PublishDafnyLanguageServerLoadErrors(DiagnosticErrorReporter errorReporter, Dafny.Program program) {
      foreach (var error in DafnyLanguageServer.LoadErrors) {
        errorReporter.Error(MessageSource.Compiler, program.GetFirstTopLevelToken(), error);
      }
    }

    private static DafnyDocument CreateDocumentWithEmptySymbolTable(
      ILogger<SymbolTable> logger,
      TextDocumentItem textDocument,
      DiagnosticErrorReporter errorReporter,
      Dafny.Program program,
      bool loadCanceled
    ) {
      return new DafnyDocument(
        textDocument,
        errorReporter,
        new List<Diagnostic>(),
        Array.Empty<Diagnostic>(),
        program,
        CreateEmptySymbolTable(program, logger),
        loadCanceled
      ) {
        ResolutionSucceeded = loadCanceled ? null : false
      };
    }

    private static SymbolTable CreateEmptySymbolTable(Dafny.Program program, ILogger<SymbolTable> logger) {
      return new SymbolTable(
        logger,
        new CompilationUnit(program),
        new Dictionary<object, ILocalizableSymbol>(),
        new Dictionary<ISymbol, SymbolLocation>(),
        new IntervalTree<Position, ILocalizableSymbol>(),
        symbolsResolved: false
      );
    }

    public Task<DafnyDocument> VerifyAsync(DafnyDocument document, CancellationToken cancellationToken) {

      return Task.Factory.StartNew(() => VerifyInternalAsync(document, cancellationToken), cancellationToken,
        TaskCreationOptions.None, LargeStackScheduler).Unwrap();
    }

    // Called only in the case there is a parsing or resolution error on the document
    public void PublishVerificationDiagnostics(DafnyDocument document) {
      diagnosticPublisher.PublishVerificationDiagnostics(document);
    }

    private async Task<DafnyDocument> VerifyInternalAsync(DafnyDocument document, CancellationToken cancellationToken) {
      notificationPublisher.SendStatusNotification(document.Text, CompilationStatus.VerificationStarted);
      document.VerificationPass = false;

      var progressReporter = new VerificationProgressReporter(
        loggerFactory.CreateLogger<VerificationProgressReporter>(),
        document, notificationPublisher, diagnosticPublisher);
      var verificationResult = await verifier.VerifyAsync(document, progressReporter, cancellationToken);
      var compilationStatusAfterVerification = verificationResult.Verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      // All unvisited trees need to set them as "verified"
      if (!cancellationToken.IsCancellationRequested) {
        SetAllUnvisitedMethodsAsVerified(document);
      }

      notificationPublisher.SendStatusNotification(document.Text, compilationStatusAfterVerification, cancellationToken.IsCancellationRequested ? "(cancelled)" : null);
      logger.LogDebug($"Finished verification with {document.Errors.ErrorCount} errors.");
      var newDocument = document with {
        OldVerificationDiagnostics = new List<Diagnostic>(),
        SerializedCounterExamples = verificationResult.SerializedCounterExamples,
        VerificationPass = true
      };
      progressReporter.ReportRealtimeDiagnostics(newDocument);
      return newDocument;
    }

    private void SetAllUnvisitedMethodsAsVerified(DafnyDocument document) {
      foreach (var tree in document.VerificationTree.Children) {
        tree.SetVerifiedIfPending();
      }
    }

    private record Request(CancellationToken CancellationToken) {
      public TaskCompletionSource<DafnyDocument> Document { get; } = new();
    }

    private class VerificationProgressReporter : IVerificationProgressReporter {
      private ICompilationStatusNotificationPublisher publisher { get; }
      private DafnyDocument document { get; }

      private ILogger<VerificationProgressReporter> logger { get; }
      private IDiagnosticPublisher diagnosticPublisher { get; }

      public VerificationProgressReporter(ILogger<VerificationProgressReporter> logger,
                                          DafnyDocument document,
                                          ICompilationStatusNotificationPublisher publisher,
                                          IDiagnosticPublisher diagnosticPublisher
      ) {
        this.document = document;
        this.publisher = publisher;
        this.logger = logger;
        this.diagnosticPublisher = diagnosticPublisher;
      }

      /// <summary>
      /// Sends a more precise verification status message to the client's status bar
      /// </summary>
      public void ReportProgress(string message) {
        publisher.SendStatusNotification(document.Text, CompilationStatus.VerificationStarted, message);
      }

      /// <summary>
      /// Fills up the document with empty verification diagnostics, one for each top-level declarations
      /// Possibly migrates previous diagnostics
      /// </summary>
      public void RecomputeVerificationTree() {
        var previousTrees = document.VerificationTree.Children;

        List<VerificationTree> result = new List<VerificationTree>();

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
          result.Add(verificationTree);
        }

        var documentFilePath = document.GetFilePath();
        foreach (var module in document.Program.Modules()) {
          foreach (var topLevelDecl in module.TopLevelDecls) {
            if (topLevelDecl is TopLevelDeclWithMembers topLevelDeclWithMembers) {
              foreach (var member in topLevelDeclWithMembers.Members) {
                if (member.tok.filename != documentFilePath) {
                  continue;
                }
                if (member is Field) {
                  if (member.BodyEndTok.line == 0) {
                    continue; // Nothing to verify
                  }
                  var diagnosticRange = member.tok.GetLspRange(member.BodyEndTok);
                  var diagnostic = new TopLevelDeclMemberVerificationTree(
                    member.Name,
                    member.CompileName,
                    member.tok.filename,
                    diagnosticRange);
                  AddAndPossiblyMigrateVerificationTree(diagnostic);
                } else if (member is Method or Function) {
                  var diagnosticRange = member.tok.GetLspRange(member.BodyEndTok.line == 0 ? member.tok : member.BodyEndTok);
                  var diagnostic = new TopLevelDeclMemberVerificationTree(
                    member.Name,
                    member.CompileName,
                    member.tok.filename,
                    diagnosticRange);
                  AddAndPossiblyMigrateVerificationTree(diagnostic);
                  if (member is Function { ByMethodBody: { } } function) {
                    var diagnosticRangeByMethod = function.ByMethodTok.GetLspRange(function.ByMethodBody.EndTok);
                    var diagnosticByMethod = new TopLevelDeclMemberVerificationTree(
                      member.Name + " by method",
                      member.CompileName + "_by_method",
                      member.tok.filename,
                      diagnosticRangeByMethod);
                    AddAndPossiblyMigrateVerificationTree(diagnosticByMethod);
                  }
                }
              }
            } else if (topLevelDecl is SubsetTypeDecl subsetTypeDecl) {
              if (subsetTypeDecl.tok.filename != documentFilePath) {
                continue;
              }
              var diagnosticRange = subsetTypeDecl.tok.GetLspRange(subsetTypeDecl.BodyEndTok);
              var diagnostic = new TopLevelDeclMemberVerificationTree(
                subsetTypeDecl.Name,
                subsetTypeDecl.CompileName,
                subsetTypeDecl.tok.filename,
                diagnosticRange);
              AddAndPossiblyMigrateVerificationTree(diagnostic);
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
      public void ReportImplementationsBeforeVerification(Implementation[] implementations) {
        if (document.LoadCanceled || implementations.Length == 0) {
          return;
        }
        // We migrate existing implementations to the new provided ones if they exist.
        // (same child number, same file and same position)
        foreach (var methodTree in document.VerificationTree.Children) {
          methodTree.ResetNewChildren();
          methodTree.ResourceCount = 0;
        }

        foreach (var implementation in implementations) {
          int priority = GetVerificationPriority(implementation.tok);

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
            logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
            continue;
          }
          var newDisplayName = targetMethodNode.DisplayName + " #" + (targetMethodNode.Children.Count + 1) + ":" +
                               implementation.Name;
          var newImplementationNode = new ImplementationVerificationTree(
            newDisplayName,
            implementation.Name,
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
            methodNode.StatusVerification = VerificationStatus.Verified;
          }
          methodNode.PropagateChildrenErrorsUp();
          methodNode.RecomputeAssertionBatchNodeDiagnostics();
        }
      }

      /// <summary>
      /// Triggers sending of the current verification diagnostics to the client
      /// </summary>
      /// <param name="dafnyDocument">The document to send. Can be a previous document</param>
      public void ReportRealtimeDiagnostics(DafnyDocument? dafnyDocument = null) {
        lock (LockProcessing) {
          dafnyDocument ??= document;
          if (dafnyDocument.LoadCanceled) {
            return;
          }
          diagnosticPublisher.PublishVerificationDiagnostics(document);
        }
      }

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
        var total = document.VerificationTree.Children.Count();
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
            ReportRealtimeDiagnostics();
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
              ConditionGeneration.Outcome.Correct => VerificationStatus.Verified,
              _ => VerificationStatus.Error
            };

            implementationNode.StatusVerification = finalOutcome;
            // Will be only executed by the last instance.
            if (!targetMethodNode.Children.All(child => child.Finished)) {
              targetMethodNode.StatusVerification = verificationResult.Outcome switch {
                ConditionGeneration.Outcome.Correct => targetMethodNode.StatusVerification,
                _ => VerificationStatus.Error
              };
            } else {
              targetMethodNode.Stop();
              ReportMethodsBeingVerified($" ({targetMethodNode.DisplayName} finished)");
              // Later, will be overriden by individual outcomes
              targetMethodNode.StatusVerification = finalOutcome;
            }

            targetMethodNode.PropagateChildrenErrorsUp();
            targetMethodNode.RecomputeAssertionBatchNodeDiagnostics();
            ReportRealtimeDiagnostics();
          }
        }
      }

      /// <summary>
      /// Called when a split is finished to be verified
      /// </summary>
      /// <param name="split">The split that was verified</param>
      /// <param name="result">The verification results for that split and per assert</param>
      public void ReportAssertionBatchResult(Split split,
        VCResult result) {
        if (document.LoadCanceled) {
          return;
        }
        lock (LockProcessing) {
          var implementation = split.Implementation;
          // While there is no error, just add successful nodes.
          var targetMethodNode = GetTargetMethodTree(implementation, out var implementationNode);
          if (targetMethodNode == null) {
            logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
          } else if (implementationNode == null) {
            logger.LogError($"No implementation node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
          } else {
            result.ComputePerAssertOutcomes(out var perAssertOutcome, out var perAssertCounterExample);

            var assertionBatchIndex = implementationNode.GetNewAssertionBatchCount();
            var assertionBatchTime = (int)result.runTime.TotalMilliseconds;
            var assertionBatchResourceCount = result.resourceCount;
            // TODO: Add assertion batches directly instead of indirectly
            implementationNode.AddAssertionBatchTime(assertionBatchTime);
            implementationNode.AddAssertionBatchResourceCount(assertionBatchResourceCount);

            // Attaches the trace
            void AddChildOutcome(Counterexample? counterexample, AssertCmd assertCmd, IToken token,
              VerificationStatus status, IToken? secondaryToken, List<IToken> relatedTokens, string? assertDisplay = "",
              string assertIdentifier = "") {
              if (token.filename != implementationNode.Filename) {
                return;
              }

              var outcomePosition = token.GetLspPosition();
              var secondaryOutcomePosition = secondaryToken?.GetLspPosition();
              var relatedRanges = relatedTokens
                .Where(tok => tok.filename == implementationNode.Filename)
                .Select(tok => tok.GetLspRange())
                .Where(range => range.Start != outcomePosition && range.Start != secondaryOutcomePosition)
                .ToList().GroupBy(x => x)
                .Select(grp => grp.FirstOrDefault())
                .OfType<Range>()
                .OrderBy(x => x.Start.Line).ToList();

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
                RelatedRanges = relatedRanges.ToImmutableList(),
                AssertionBatchIndex = assertionBatchIndex,
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
              List<IToken> RelatedPositions = counterexample != null ?
                counterexample.Trace.SelectMany(block => {
                  var tokens = new List<IToken>();
                  if (block.TransferCmd != null) {
                    tokens.Add(block.TransferCmd.tok);
                  }
                  tokens.AddRange(block.cmds.Select(cmd => cmd.tok));
                  return tokens;
                }).ToList() : new List<IToken>();
              if (assertCmd is AssertEnsuresCmd assertEnsuresCmd) {
                AddChildOutcome(counterexample, assertCmd, assertEnsuresCmd.Ensures.tok, status, secondaryToken, RelatedPositions, " ensures", "_ensures");
              } else if (assertCmd is AssertRequiresCmd assertRequiresCmd) {
                AddChildOutcome(counterexample, assertCmd, assertRequiresCmd.Call.tok, status, secondaryToken, RelatedPositions, assertDisplay: "Call", assertIdentifier: "call");
              } else {
                AddChildOutcome(counterexample, assertCmd, assertCmd.tok, status, secondaryToken, RelatedPositions, assertDisplay: "Assertion", assertIdentifier: "assert");
              }
            }
            targetMethodNode.PropagateChildrenErrorsUp();
            targetMethodNode.RecomputeAssertionBatchNodeDiagnostics();
            ReportRealtimeDiagnostics();
          }
        }
      }

      /// <summary>
      /// Returns the verification priority for a given token.
      /// </summary>
      /// <param name="token">The token to consider</param>
      /// <returns>The automatically set priority for the underlying method, or 0</returns>
      private int GetVerificationPriority(IToken token) {
        return 0;
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
      private static VerificationStatus GetNodeStatus(ProverInterface.Outcome outcome) {
        return outcome switch {
          ProverInterface.Outcome.Valid => VerificationStatus.Verified,
          ProverInterface.Outcome.Invalid => VerificationStatus.Error,
          ProverInterface.Outcome.Undetermined => VerificationStatus.Inconclusive,
          ProverInterface.Outcome.TimeOut => VerificationStatus.Error,
          ProverInterface.Outcome.OutOfMemory => VerificationStatus.Error,
          ProverInterface.Outcome.OutOfResource => VerificationStatus.Error,
          ProverInterface.Outcome.Bounded => VerificationStatus.Error,
          _ => VerificationStatus.Error
        };
      }
    }
  }
}
