using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
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
    private readonly BlockingCollection<Request> requestQueue = new();
    private readonly IOptions<DafnyPluginsOptions> dafnyPluginsOptions;
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
      IOptions<DafnyPluginsOptions> dafnyPluginsOptions, IDiagnosticPublisher diagnosticPublisher) {
      this.parser = parser;
      this.symbolResolver = symbolResolver;
      this.verifier = verifier;
      this.symbolTableFactory = symbolTableFactory;
      this.ghostStateDiagnosticCollector = ghostStateDiagnosticCollector;
      this.notificationPublisher = notificationPublisher;
      this.loggerFactory = loggerFactory;
      this.logger = loggerFactory.CreateLogger<TextDocumentLoader>();
      this.dafnyPluginsOptions = dafnyPluginsOptions;
      this.diagnosticPublisher = diagnosticPublisher;
    }

    public static TextDocumentLoader Create(
      IDafnyParser parser,
      ISymbolResolver symbolResolver,
      IProgramVerifier verifier,
      ISymbolTableFactory symbolTableFactory,
      IGhostStateDiagnosticCollector ghostStateDiagnosticCollector,
      ICompilationStatusNotificationPublisher notificationPublisher,
      ILoggerFactory loggerFactory,
      IOptions<DafnyPluginsOptions> compilerOptions,
      IDiagnosticPublisher diagnosticPublisher
      ) {
      var loader = new TextDocumentLoader(loggerFactory, parser, symbolResolver, verifier, symbolTableFactory, ghostStateDiagnosticCollector, notificationPublisher, compilerOptions, diagnosticPublisher);
      var loadThread = new Thread(loader.Run, MaxStackSize) { IsBackground = true };
      loadThread.Start();
      return loader;
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

    public async Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var request = new LoadRequest(textDocument, cancellationToken);
      requestQueue.Add(request, cancellationToken);
      return await request.Document.Task;
    }

    private void Run() {
      foreach (var request in requestQueue.GetConsumingEnumerable()) {
        if (request.CancellationToken.IsCancellationRequested) {
          request.Document.SetCanceled(request.CancellationToken);
          continue;
        }
        try {
          var document = request switch {
            LoadRequest loadRequest => LoadInternal(loadRequest),
            VerifyRequest verifyRequest => VerifyInternal(verifyRequest),
            _ => throw new ArgumentException($"invalid request type ${request.GetType()}")
          };
          request.Document.SetResult(document);
        } catch (OperationCanceledException e) {
          request.Document.SetCanceled(e.CancellationToken);
        } catch (Exception e) {
          request.Document.SetException(e);
        }
      }
    }

    private DafnyDocument LoadInternal(LoadRequest loadRequest) {
      var (textDocument, cancellationToken) = loadRequest;
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

    public async Task<DafnyDocument> VerifyAsync(DafnyDocument document, CancellationToken cancellationToken) {
      var request = new VerifyRequest(document, cancellationToken);
      requestQueue.Add(request, cancellationToken);
      return await request.Document.Task;
    }

    private void RecomputeVerificationNodeDiagnostics(DafnyDocument document) {
      var previousDiagnostics = document.VerificationNodeDiagnostic.Children;

      List<NodeDiagnostic> result = new List<NodeDiagnostic>();

      void AddAndPossiblyMigrateDiagnostic(NodeDiagnostic nodeDiagnostic) {
        var position = nodeDiagnostic.Position;
        var previousDiagnostic = previousDiagnostics.FirstOrDefault(
          oldNode => oldNode != null && oldNode.Position == position,
          null);
        if (previousDiagnostic != null) {
          previousDiagnostic.SetObsolete();
          nodeDiagnostic.StatusVerification = previousDiagnostic.StatusVerification;
          nodeDiagnostic.StatusCurrent = CurrentStatus.Obsolete;
          nodeDiagnostic.Children = previousDiagnostic.Children;
        }
        result.Add(nodeDiagnostic);
      }

      var documentFilePath = document.GetFilePath();
      foreach (var module in document.Program.Modules()) {
        foreach (var topLevelDecl in module.TopLevelDecls) {
          if (topLevelDecl is TopLevelDeclWithMembers topLevelDeclWithMembers) {
            foreach (var member in topLevelDeclWithMembers.Members) {
              if (member is Method or Function) {
                if (member.tok.filename != documentFilePath) {
                  continue;
                }
                var diagnosticRange = member.tok.GetLspRange(member.BodyEndTok.line == 0 ? member.tok : member.BodyEndTok);
                var diagnostic = new MethodOrSubsetTypeNodeDiagnostic(
                  member.Name,
                  member.CompileName,
                  member.tok.filename,
                  diagnosticRange);
                AddAndPossiblyMigrateDiagnostic(diagnostic);
                if (member is Function { ByMethodBody: { } } function) {
                  var diagnosticRangeByMethod = function.ByMethodTok.GetLspRange(function.ByMethodBody.EndTok);
                  var diagnosticByMethod = new MethodOrSubsetTypeNodeDiagnostic(
                    member.Name + " by method",
                    member.CompileName + "_by_method",
                    member.tok.filename,
                    diagnosticRangeByMethod);
                  AddAndPossiblyMigrateDiagnostic(diagnosticByMethod);
                }
              }
            }
          } else if (topLevelDecl is SubsetTypeDecl subsetTypeDecl) {
            if (subsetTypeDecl.tok.filename != documentFilePath) {
              continue;
            }

            var diagnosticPosition = subsetTypeDecl.tok.GetLspPosition();
            if (subsetTypeDecl.Witness == null) {
              continue;
            }
            var diagnosticRange = new Range(diagnosticPosition,
                subsetTypeDecl.Witness.tok.GetLspPosition(true));
            var diagnostic = new MethodOrSubsetTypeNodeDiagnostic(
              subsetTypeDecl.Name,
              subsetTypeDecl.CompileName,
              subsetTypeDecl.tok.filename,
              diagnosticRange);
            AddAndPossiblyMigrateDiagnostic(diagnostic);
          }
        }
      }
      document.VerificationNodeDiagnostic.Children = result;
    }

    private DafnyDocument VerifyInternal(VerifyRequest verifyRequest) {
      var (document, cancellationToken) = verifyRequest;
      notificationPublisher.SendStatusNotification(document.Text, CompilationStatus.VerificationStarted);
      document.VerificationPass = false;
      RecomputeVerificationNodeDiagnostics(document);
      diagnosticPublisher.PublishVerificationDiagnostics(document);
      var progressReporter = new VerificationProgressReporter(
        loggerFactory.CreateLogger<VerificationProgressReporter>(),
        document, notificationPublisher, diagnosticPublisher);
      var verificationResult = verifier.Verify(document, progressReporter, cancellationToken);
      var compilationStatusAfterVerification = verificationResult.Verified
        ? CompilationStatus.VerificationSucceeded
        : CompilationStatus.VerificationFailed;
      // All unvisited nodes need to set them as "verified"
      if (!cancellationToken.IsCancellationRequested) {
        SetAllUnvisitedMethodsAsVerified(document);
      }

      notificationPublisher.SendStatusNotification(document.Text, compilationStatusAfterVerification);
      logger.LogDebug($"Finished verification with {document.Errors.ErrorCount} errors.");
      return document with {
        OldVerificationDiagnostics = new List<Diagnostic>(),
        SerializedCounterExamples = verificationResult.SerializedCounterExamples,
        VerificationPass = true
      };
    }

    private void SetAllUnvisitedMethodsAsVerified(DafnyDocument document) {
      var updated = false;
      foreach (var node in document.VerificationNodeDiagnostic.Children) {
        updated = node.SetVerifiedIfPending() || updated;
      }

      if (updated) {
        diagnosticPublisher.PublishVerificationDiagnostics(document);
      }
    }

    private record Request(CancellationToken CancellationToken) {
      public TaskCompletionSource<DafnyDocument> Document { get; } = new();
    }

    private record LoadRequest(TextDocumentItem TextDocument, CancellationToken CancellationToken) : Request(CancellationToken);

    private record VerifyRequest(DafnyDocument OriginalDocument, CancellationToken CancellationToken) : Request(CancellationToken);

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

      public void ReportProgress(string message) {
        publisher.SendStatusNotification(document.Text, CompilationStatus.VerificationStarted, message);
      }

      public void ReportImplementationsBeforeVerification(Implementation[] implementations) {
        if (document.LoadCanceled || implementations.Length == 0) {
          return;
        }
        // We migrate existing implementations to the new provided ones if they exist.
        // (same child number, same file and same position)
        foreach (var methodNode in document.VerificationNodeDiagnostic.Children) {
          methodNode.ResetNewChildren();
          methodNode.ResourceCount = 0;
        }

        foreach (var implementation in implementations) {
          var targetMethodNode = GetTargetMethodNode(implementation, out var oldImplementationNode, true);
          if (targetMethodNode == null) {
            logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
            continue;
          }
          var newDisplayName = targetMethodNode.DisplayName + " #" + (targetMethodNode.Children.Count + 1) + ":" +
                               implementation.Name;
          var newImplementationNode = new ImplementationNodeDiagnostic(
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

        foreach (var methodNode in document.VerificationNodeDiagnostic.Children.OfType<MethodOrSubsetTypeNodeDiagnostic>()) {
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

      private void ReportMethodsBeingVerified(string extra = "") {
        var pending = document.VerificationNodeDiagnostic.Children
          .Where(diagnostic => diagnostic.Started && !diagnostic.Finished)
          .OrderBy(diagnostic => diagnostic.StartTime)
          .Select(diagnostic => diagnostic.DisplayName);
        var message = string.Join(", ", pending) + extra;
        ReportProgress(message);
      }

      public void ReportStartVerifyImplementation(Implementation implementation) {
        if (document.LoadCanceled) {
          return;
        }

        lock (LockProcessing) {
          var targetMethodNode = GetTargetMethodNode(implementation, out var implementationNode);
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
            diagnosticPublisher.PublishVerificationDiagnostics(document);
          }
        }
      }

      public void ReportEndVerifyImplementation(Implementation implementation, VerificationResult verificationResult) {
        if (document.LoadCanceled) {
          return;
        }
        var targetMethodNode = GetTargetMethodNode(implementation, out var implementationNode);
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
            diagnosticPublisher.PublishVerificationDiagnostics(document);
          }
        }
      }

      public void ReportAssertionBatchResult(Split split,
        Dictionary<AssertCmd, ConditionGeneration.Outcome> perAssertOutcome,
        Dictionary<AssertCmd, Counterexample> perAssertCounterExample) {
        if (document.LoadCanceled) {
          return;
        }
        lock (LockProcessing) {
          var implementation = split.Implementation;
          // While there is no error, just add successful nodes.
          var targetMethodNode = GetTargetMethodNode(implementation, out var implementationNode);
          if (targetMethodNode == null) {
            logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
          } else if (implementationNode == null) {
            logger.LogError($"No implementation node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
          } else {
            var assertionBatchIndex = implementationNode.GetNewAssertionBatchCount();
            var assertionBatchTime = (int)split.Checker.ProverRunTime.TotalMilliseconds;
            var assertionBatchResourceCount = split.Checker.GetProverResourceCount().GetAwaiter().GetResult();
            implementationNode.AddAssertionBatchTime(assertionBatchTime);
            implementationNode.AddAssertionBatchResourceCount(assertionBatchResourceCount);

            // Attaches the trace
            void AddChildOutcome(IToken token,
              VerificationStatus status, IToken? secondaryToken, List<IToken> relatedTokens, string? assertDisplay = "", string assertIdentifier = "") {
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
              var nodeDiagnostic = new AssertionNodeDiagnostic(
                $"{targetMethodNode.DisplayName}{assertDisplay} #{childrenCount}",
                $"{targetMethodNode.Identifier}_{childrenCount}{assertIdentifier}",
                token.filename,
                secondaryOutcomePosition,
                outcomeRange
              ) {
                StatusVerification = status,
                StatusCurrent = CurrentStatus.Current,
                RelatedRanges = relatedRanges,
                AssertionBatchIndex = assertionBatchIndex
              }.WithDuration(implementationNode.StartTime, assertionBatchTime);
              // Add this diagnostics as the new one to display once the implementation is fully verified
              implementationNode.AddNewChild(nodeDiagnostic);
              // Update any previous pending "verifying" diagnostic as well so that they are updated in real-time
              var previousChild = implementationNode.Children.OfType<AssertionNodeDiagnostic>()
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
                AddChildOutcome(assertEnsuresCmd.Ensures.tok, status, secondaryToken, RelatedPositions, " ensures", "_ensures");
                if (secondaryToken != null) {
                  var returnPosition = secondaryToken.GetLspPosition();
                  if (returnPosition != implementationNode.Position) {
                    AddChildOutcome(secondaryToken, status, assertEnsuresCmd.tok, RelatedPositions, "return branch",
                      "_return");
                  }
                }
              } else if (assertCmd is AssertRequiresCmd assertRequiresCmd) {
                AddChildOutcome(assertRequiresCmd.Call.tok, status, secondaryToken, RelatedPositions, "Call", "call");
              } else {
                AddChildOutcome(assertCmd.tok, status, secondaryToken, RelatedPositions, "Assertion", "assert");
                if (secondaryToken != null) {
                  var requiresPosition = secondaryToken.GetLspPosition();
                  if (targetMethodNode.Range.Contains(requiresPosition)) {
                    AddChildOutcome(secondaryToken, status, assertCmd.tok, RelatedPositions, "Call precondition",
                      "call_precondition");
                  }
                }
              }
            }
            targetMethodNode.PropagateChildrenErrorsUp();
            targetMethodNode.RecomputeAssertionBatchNodeDiagnostics();
            diagnosticPublisher.PublishVerificationDiagnostics(document);
          }
        }
      }

      // For realtime per-split verification, when verification is migrated

      public int GetVerificationPriority(IToken implTok) {
        var lastChange = document.LastChange;
        if (lastChange == null) {
          return 0;
        }

        var implPosition = implTok.GetLspPosition(); ;
        // We might want to simplify this quadratic algorithm
        var method = document.VerificationNodeDiagnostic.Children.FirstOrDefault(node =>
          node != null && node.Range.Contains(implPosition), null);
        if (method != null) {
          if (method.Range.Intersects(lastChange)) {
            RememberLastTouchedMethod(method);
            return 10;
          }
          // 0 if not found
          var priority = 1 + document.LastTouchedMethodPositions.IndexOf(method.Position);
          return priority;
        }
        // Can we do the call graph?
        return 0;
      }

      private void RememberLastTouchedMethod(NodeDiagnostic method) {
        var index = document.LastTouchedMethodPositions.IndexOf(method.Position);
        if (index != -1) {
          document.LastTouchedMethodPositions.RemoveAt(index);
        }
        document.LastTouchedMethodPositions.Add(method.Position);
        while (document.LastTouchedMethodPositions.Count() > 5) {
          document.LastTouchedMethodPositions.RemoveAt(0);
        }
      }



      private MethodOrSubsetTypeNodeDiagnostic? GetTargetMethodNode(Implementation implementation, out ImplementationNodeDiagnostic? implementationNode, bool nameBased = false) {
        var targetMethodNode = document.VerificationNodeDiagnostic.Children.OfType<MethodOrSubsetTypeNodeDiagnostic>().FirstOrDefault(
          node => node?.Position == implementation.tok.GetLspPosition() && node?.Filename == implementation.tok.filename
          , null);
        if (nameBased) {
          implementationNode = targetMethodNode?.Children.OfType<ImplementationNodeDiagnostic>().FirstOrDefault(
            node => {
              var nodeImpl = node?.GetImplementation();
              return nodeImpl?.Name == implementation.Name;
            }, null);
        } else {
          implementationNode = targetMethodNode?.Children.OfType<ImplementationNodeDiagnostic>().FirstOrDefault(
            node => node?.GetImplementation() == implementation, null);
        }

        return targetMethodNode;
      }

      private readonly object LockProcessing = new();


      private static VerificationStatus GetNodeStatus(ConditionGeneration.Outcome outcome) {
        return outcome switch {
          ConditionGeneration.Outcome.Correct => VerificationStatus.Verified,
          ConditionGeneration.Outcome.Errors => VerificationStatus.Error,
          ConditionGeneration.Outcome.Inconclusive => VerificationStatus.Inconclusive,
          ConditionGeneration.Outcome.ReachedBound => VerificationStatus.Error,
          ConditionGeneration.Outcome.SolverException => VerificationStatus.Error,
          ConditionGeneration.Outcome.TimedOut => VerificationStatus.Error,
          ConditionGeneration.Outcome.OutOfMemory => VerificationStatus.Error,
          ConditionGeneration.Outcome.OutOfResource => VerificationStatus.Error,
          _ => VerificationStatus.Error
        };
      }
    }
  }
}
