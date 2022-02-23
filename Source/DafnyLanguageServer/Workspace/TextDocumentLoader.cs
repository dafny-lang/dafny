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
      foreach (var module in document.Program.Modules()) {
        foreach (var toplLevelDecl in module.TopLevelDecls) {
          if (toplLevelDecl is TopLevelDeclWithMembers topLevelDeclWithMembers) {
            foreach (var member in topLevelDeclWithMembers.Members) {
              if (member is Method or Function) {
                var diagnosticPosition = TokenToPosition(member.tok);
                var diagnosticRange = new Range(diagnosticPosition, TokenToPosition(member.BodyEndTok, true));
                var diagnostic = new NodeDiagnostic(member.Name, member.CompileName, member.tok.filename,
                  diagnosticPosition, diagnosticRange);
                var previousDiagnostic = previousDiagnostics.FirstOrDefault(
                  oldNode => oldNode != null && oldNode.Position == diagnosticPosition,
                  null);
                if (previousDiagnostic != null) {
                  diagnostic.Status = previousDiagnostic.Status;
                  diagnostic.Children = previousDiagnostic.Children;
                }
                result.Add(diagnostic);
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

      public void ReportImplementationMultiplicity(IToken[] implementationPositions) {
        foreach (var node in document.VerificationNodeDiagnostic.Children) {
          node.ImplementationCount = 0;
          node.VerifiedImplementationCount = 0;
        }

        foreach (var token in implementationPositions) {
          var targetMethodNode = GetTargetMethodNode(token);
          if (targetMethodNode != null) {
            targetMethodNode.ImplementationCount++;
          }
        }
      }

      public void ReportStartVerifyMethodOrFunction(IToken implToken) {
        var targetMethodNode = GetTargetMethodNode(implToken);
        if (targetMethodNode == null) {
          logger.LogError($"No method at {implToken}");
        } else {
          if (!targetMethodNode.Started) { // The same method could be started multiple times for each implementation
            targetMethodNode.Start();
            diagnosticPublisher.PublishVerificationDiagnostics(document);
          }
        }
      }

      private NodeDiagnostic? GetTargetMethodNode(IToken implToken) {
        return document.VerificationNodeDiagnostic.Children.FirstOrDefault(
          node => node?.Position == TokenToPosition(implToken) && node?.Filename == implToken.filename
          , null);
      }

      public void ReportEndVerifyMethodOrFunction(IToken implToken, VerificationResult verificationResult) {
        var targetMethodNode = document.VerificationNodeDiagnostic.Children.FirstOrDefault(node => node?.Position == TokenToPosition(implToken), null);
        if (targetMethodNode == null) {
          logger.LogError($"No method at {implToken}");
        } else {
          int newVerifiedCount;
          lock (targetMethodNode) {
            newVerifiedCount = ++targetMethodNode.VerifiedImplementationCount;
            if (verificationResult.Errors != null) {
              var errorCount = targetMethodNode.NewChildrenCount + 1;

              void AddChildError(IToken token, string errorDisplay = "", string errorIdentifier = "") {
                var errorPosition = TokenToPosition(token);
                if (targetMethodNode.Filename != token.filename) {
                  return;
                }

                errorDisplay = errorDisplay != "" ? " " + errorDisplay : "";
                errorIdentifier = errorIdentifier != "" ? "_" + errorIdentifier : "";

                var errorRange = new Range(errorPosition, TokenToPosition(token, true));
                var nodeDiagnostic = new NodeDiagnostic(
                  $"{targetMethodNode.DisplayName}{errorDisplay} #{errorCount}",
                  $"{targetMethodNode.Identifier}_{errorCount}{errorIdentifier}",
                  token.filename,
                  errorPosition,
                  errorRange
                ) {
                  Status = NodeVerificationStatus.Error
                };
                targetMethodNode.AddNewChild(nodeDiagnostic);
              }

              foreach (var error in verificationResult.Errors) {
                if (error is ReturnCounterexample returnError) {
                  AddChildError(returnError.FailingEnsures.tok, "", "");
                  var returnPosition = TokenToPosition(returnError.FailingReturn.tok);
                  if (returnPosition != targetMethodNode.Position) {
                    AddChildError(returnError.FailingReturn.tok, "return branch", "_return");
                    // TODO: Dynamic range highlighting + display error on postconditions of edited code
                  }
                } else if (error is AssertCounterexample assertError) {
                  AddChildError(assertError.FailingAssert.tok, "Assertion", "assert");
                } else if (error is CallCounterexample callError) {
                  AddChildError(callError.FailingCall.tok, "Call", "call");
                  if (targetMethodNode.Range.Contains(TokenToPosition(callError.FailingRequires.tok))) {
                    AddChildError(callError.FailingCall.tok, "Call precondition", "call_precondition");
                  }
                }
                errorCount++;
              }
            }

            if (newVerifiedCount == targetMethodNode.ImplementationCount) {
              targetMethodNode.SaveNewChildren();
            }
            targetMethodNode.ResourceCount = (newVerifiedCount == 1 ? 0 : targetMethodNode.ResourceCount) + verificationResult.ResourceCount;
          }

          // Will be only executed by the last instance.
          if (newVerifiedCount < targetMethodNode.ImplementationCount) {
            targetMethodNode.Status = verificationResult.Outcome switch {
              ConditionGeneration.Outcome.Correct => targetMethodNode.Status,
              _ => NodeVerificationStatus.Error
            };
            targetMethodNode.RecomputeStatus();
          } else {
            targetMethodNode.Stop();
            // Later, will be overriden by individual outcomes
            targetMethodNode.Status = verificationResult.Outcome switch {
              ConditionGeneration.Outcome.Correct => NodeVerificationStatus.Verified,
              _ => NodeVerificationStatus.Error
            };
            targetMethodNode.RecomputeStatus();
          }

          diagnosticPublisher.PublishVerificationDiagnostics(document);
        }
      }

      public void ReportVerificationStarts(List<IToken> assertionToken, IToken implToken) {
        // TODO: Either migrate or create node diagnostics
      }

      public void ReportVerificationCompleted(List<IToken> assertionToken, IToken implToken,
        ConditionGeneration.Outcome outcome, int totalResource) {
        // TODO: update node diagnostics
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
