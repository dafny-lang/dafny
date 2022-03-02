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
using Microsoft.CodeAnalysis.CSharp.Syntax;
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
          nodeDiagnostic.Status = previousDiagnostic.Status;
          nodeDiagnostic.Children = previousDiagnostic.Children;
        }
        result.Add(nodeDiagnostic);
      }

      var documentFilePath = document.GetFilePath();
      foreach (var module in document.Program.Modules()) {
        foreach (var toplLevelDecl in module.TopLevelDecls) {
          if (toplLevelDecl is TopLevelDeclWithMembers topLevelDeclWithMembers) {
            foreach (var member in topLevelDeclWithMembers.Members) {
              if (member is Method or Function) {
                if (member.tok.filename != documentFilePath) {
                  continue;
                }
                var diagnosticPosition = TokenToPosition(member.tok);
                var diagnosticRange = new Range(diagnosticPosition, TokenToPosition(member.BodyEndTok, true));
                var diagnostic = new NodeDiagnostic(
                  member.Name,
                  member.CompileName,
                  member.tok.filename,
                  diagnosticPosition,
                  new(),
                  diagnosticRange,
                  true);
                AddAndPossiblyMigrateDiagnostic(diagnostic);
                if (member is Function { ByMethodBody: { } } function) {
                  var diagnosticPositionByMethod = TokenToPosition(function.ByMethodTok);
                  var diagnosticRangeByMethod = new Range(diagnosticPositionByMethod, TokenToPosition(function.ByMethodBody.EndTok, true));
                  var diagnosticByMethod = new NodeDiagnostic(
                    member.Name + " by method",
                    member.CompileName + "_by_method",
                    member.tok.filename,
                    diagnosticPositionByMethod,
                    new(),
                    diagnosticRangeByMethod, true);
                  AddAndPossiblyMigrateDiagnostic(diagnosticByMethod);
                }
              }
            }
          }
        }
      }
      document.VerificationNodeDiagnostic.Children = result;
    }

    private static Position TokenToPosition(IToken token, bool end = false) {
      return new Position(token.line, token.col + (end ? token.val.Length : 0));
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
      // All unvisited nodes that were not verified, we need to set them as "verified"
      if (!cancellationToken.IsCancellationRequested) {
        SetAllUnvisitedMethodsAsVerified(document);
      }

      notificationPublisher.SendStatusNotification(document.Text, compilationStatusAfterVerification);
      // TODO: ability to recover previous positions so that we don't need to start from scratch.
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
          var newImplementationNode = new NodeDiagnostic(
            newDisplayName,
            implementation.Name,
            targetMethodNode.Filename,
            targetMethodNode.Position,
            new(),
            targetMethodNode.Range,
            true
          ).WithImplementation(implementation);
          if (oldImplementationNode != null) {
            newImplementationNode.Children = oldImplementationNode.Children;
          }
          targetMethodNode?.AddNewChild(newImplementationNode);
        }

        foreach (var methodNode in document.VerificationNodeDiagnostic.Children) {
          methodNode.SaveNewChildren();
        }
      }

      public void ReportStartVerifyImplementation(Implementation implementation) {
        var targetMethodNode = GetTargetMethodNode(implementation, out var implementationNode);
        if (targetMethodNode == null) {
          logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
        } else {
          if (!targetMethodNode.Started) {
            // The same method could be started multiple times for each implementation
            targetMethodNode.Start();
          }

          if (implementationNode == null) {
            logger.LogError($"No implementation at {implementation.tok}");
          } else {
            implementationNode.AssertionBatchCount = 0;
            implementationNode.Start();
          }

          diagnosticPublisher.PublishVerificationDiagnostics(document);
        }
      }

      private NodeDiagnostic? GetTargetMethodNode(Implementation implementation, out NodeDiagnostic? implementationNode, bool nameBased = false) {
        var targetMethodNode = document.VerificationNodeDiagnostic.Children.FirstOrDefault(
          node => node?.Position == TokenToPosition(implementation.tok) && node?.Filename == implementation.tok.filename
          , null);
        if (nameBased) {
          implementationNode = targetMethodNode?.Children.FirstOrDefault(
            node => {
              var nodeImpl = node?.GetImplementation();
              return nodeImpl?.Name == implementation.Name;
            }, null);
        } else {
          implementationNode = targetMethodNode?.Children.FirstOrDefault(
            node => node?.GetImplementation() == implementation, null);
        }

        return targetMethodNode;
      }

      private object LockProcessing = new();

      public void ReportEndVerifyImplementation(Implementation implementation, VerificationResult verificationResult) {
        var targetMethodNode = GetTargetMethodNode(implementation, out var implementationNode);
        if (targetMethodNode == null) {
          logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
        } else if (implementationNode == null) {
          logger.LogError($"No implementation node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
        } else {
          implementationNode.Stop();
          implementationNode.ResourceCount = verificationResult.ResourceCount;
          implementationNode.SaveNewChildren();

          lock (LockProcessing) {
            targetMethodNode.ResourceCount += verificationResult.ResourceCount;
            // Will be only executed by the last instance.
            if (!targetMethodNode.Children.All(child => child.Finished)) {
              targetMethodNode.Status = verificationResult.Outcome switch {
                ConditionGeneration.Outcome.Correct => targetMethodNode.Status,
                _ => NodeVerificationStatus.Error
              };
            } else {
              targetMethodNode.Stop();
              // Later, will be overriden by individual outcomes
              targetMethodNode.Status = verificationResult.Outcome switch {
                ConditionGeneration.Outcome.Correct => NodeVerificationStatus.Verified,
                _ => NodeVerificationStatus.Error
              };
            }

            targetMethodNode.RecomputeStatus();
            diagnosticPublisher.PublishVerificationDiagnostics(document);
          }
        }
      }

      public static NodeVerificationStatus GetNodeStatus(ConditionGeneration.Outcome outcome) {
        return outcome switch {
          ConditionGeneration.Outcome.Correct => NodeVerificationStatus.Verified,
          ConditionGeneration.Outcome.Errors => NodeVerificationStatus.Error,
          ConditionGeneration.Outcome.Inconclusive => NodeVerificationStatus.Inconclusive,
          ConditionGeneration.Outcome.ReachedBound => NodeVerificationStatus.Error,
          ConditionGeneration.Outcome.SolverException => NodeVerificationStatus.Error,
          ConditionGeneration.Outcome.TimedOut => NodeVerificationStatus.Error,
          ConditionGeneration.Outcome.OutOfMemory => NodeVerificationStatus.Error,
          ConditionGeneration.Outcome.OutOfResource => NodeVerificationStatus.Error,
          _ => NodeVerificationStatus.Inconclusive
        };
      }

      public void ReportAssertionBatchResult(
          Implementation implementation,
          Dictionary<AssertCmd, ConditionGeneration.Outcome> perAssertOutcome,
          Dictionary<AssertCmd, Counterexample> perAssertCounterExample) {
        // While there is no error, just add successful nodes.
        var targetMethodNode = GetTargetMethodNode(implementation, out var implementationNode);
        if (targetMethodNode == null) {
          logger.LogError($"No method node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
        } else if (implementationNode == null) {
          logger.LogError($"No implementation node at {implementation.tok.filename}:{implementation.tok.line}:{implementation.tok.col}");
        } else {
          lock (LockProcessing) {
            implementationNode.AssertionBatchCount += 1;
            // TODO: Attach the full trace if possible
            void AddChildOutcome(IToken token,
              NodeVerificationStatus status, IToken? secondaryToken, List<IToken> relatedTokens, string? assertDisplay = "", string assertIdentifier = "") {
              if (token.filename != implementationNode.Filename) {
                return;
              }

              var relatedPositions = relatedTokens
                .Where(tok => tok.filename == implementationNode.Filename)
                .Select(tok => TokenToPosition(tok)).ToList();
              var outcomePosition = TokenToPosition(token);
              var secondaryOutcomePosition = secondaryToken != null ? TokenToPosition(secondaryToken) : null;

              var childrenCount = implementationNode.GetNewChildrenCount();
              assertDisplay = assertDisplay != "" ? " " + assertDisplay : "";
              assertIdentifier = assertIdentifier != "" ? "_" + assertIdentifier : "";

              var outcomeRange = new Range(outcomePosition, TokenToPosition(token, true));
              var nodeDiagnostic = new NodeDiagnostic(
                $"{targetMethodNode.DisplayName}{assertDisplay} #{childrenCount}",
                $"{targetMethodNode.Identifier}_{childrenCount}{assertIdentifier}",
                token.filename,
                outcomePosition,
                secondaryOutcomePosition,
                outcomeRange,
                false
              ) {
                Status = status,
                RelatedPositions = relatedPositions
              };
              // Add this diagnostics as the new one to display once the implementation is fully verified
              implementationNode.AddNewChild(nodeDiagnostic);
              // Update any previous pending "verifying" diagnostic as well so that they are updated in real-time
              var previousChild = implementationNode.Children.FirstOrDefault(child =>
                child != null && child.Position == outcomePosition && (
                  secondaryOutcomePosition == null ||
                  secondaryOutcomePosition == child.SecondaryPosition), null);
              if (previousChild != null) {
                implementationNode.Children.Remove(previousChild);
                implementationNode.Children.Add(previousChild with {
                  Status = status
                });
              }
            }

            foreach (var (assertCmd, outcome) in perAssertOutcome) {
              var status = GetNodeStatus(outcome);
              perAssertCounterExample.TryGetValue(assertCmd, out var counterexample);
              IToken? secondaryToken = counterexample is ReturnCounterexample returnCounterexample ? returnCounterexample.FailingReturn.tok :
                counterexample is CallCounterexample callCounterexample ? callCounterexample.FailingRequires.tok :
                null;
              List<IToken> RelatedPositions = counterexample != null ?
                counterexample.Trace.Select(block => block.TransferCmd?.tok).OfType<IToken>().ToList() : new();
              if (assertCmd is AssertEnsuresCmd assertEnsuresCmd) {
                AddChildOutcome(assertEnsuresCmd.Ensures.tok, status, secondaryToken, RelatedPositions, " ensures", "_ensures");
                if (secondaryToken == null) {
                  continue;
                }
                var returnPosition = TokenToPosition(secondaryToken);
                if (returnPosition != implementationNode.Position) {
                  AddChildOutcome(secondaryToken, status, assertEnsuresCmd.tok, RelatedPositions, "return branch", "_return");
                }
              } else if (assertCmd is AssertRequiresCmd assertRequiresCmd) {
                AddChildOutcome(assertRequiresCmd.Call.tok, status, secondaryToken, RelatedPositions, "Call", "call");
              } else {
                AddChildOutcome(assertCmd.tok, status, secondaryToken, RelatedPositions, "Assertion", "assert");
                if (secondaryToken == null) {
                  continue;
                }
                var requiresPosition = TokenToPosition(secondaryToken);
                if (targetMethodNode.Range.Contains(requiresPosition)) {
                  AddChildOutcome(secondaryToken, status, assertCmd.tok, RelatedPositions, "Call precondition", "call_precondition");
                }
              }
            }

            implementationNode.RecomputeStatus();
          }

          diagnosticPublisher.PublishVerificationDiagnostics(document);
        }
      }

      // For realtime per-split verification, when verification is migrated
      public void ReportErrorFindItsMethod(IToken tok, string message) {
        // TODO: update node diagnostics
      }

      public int GetVerificationPriority(IToken implTok) {
        var lastChange = document.LastChange;
        if (lastChange == null) {
          return 0;
        }
        var implPosition = TokenToPosition(implTok);
        // We might want to simplify this quadratic algorithm
        var method = document.VerificationNodeDiagnostic.Children.FirstOrDefault(node =>
          node != null && node.Position == implPosition, null);
        if (method != null) {
          if (method.Range.Intersects(lastChange)) {
            RememberLastTouchedMethod(method);
            return 10;
          }
          // 0 if not found
          var priority = 1 + document.LastTouchedMethods.IndexOf(method.Position);
          return priority;
        }
        // Can we do the call graph?
        return 0;
      }

      private void RememberLastTouchedMethod(NodeDiagnostic method) {
        var index = document.LastTouchedMethods.IndexOf(method.Position);
        if (index != -1) {
          document.LastTouchedMethods.RemoveAt(index);
        }
        document.LastTouchedMethods.Add(method.Position);
        while (document.LastTouchedMethods.Count() > 5) {
          document.LastTouchedMethods.RemoveAt(0);
        }
      }
    }
  }
}
