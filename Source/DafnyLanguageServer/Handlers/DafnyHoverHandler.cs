using System;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnyHoverHandler : HoverHandlerBase {
    // TODO add the range of the name to the hover.
    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;

    public DafnyHoverHandler(ILogger<DafnyHoverHandler> logger, IDocumentDatabase documents) {
      this.logger = logger;
      this.documents = documents;
    }

    protected override HoverRegistrationOptions CreateRegistrationOptions(HoverCapability capability, ClientCapabilities clientCapabilities) {
      return new HoverRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public async override Task<Hover?> Handle(HoverParams request, CancellationToken cancellationToken) {
      logger.LogTrace("received hover request for {Document}", request.TextDocument);
      var document = await documents.GetDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("the document {Document} is not loaded", request.TextDocument);
        return null;
      }
      if (!document.SymbolTable.TryGetSymbolAt(request.Position, out var symbol)) {
        var hover = GetDiagnosticsHover(document, request.Position);
        if (hover != null) {
          return hover;
        }
        logger.LogDebug("no symbol was found at {Position} in {Document}", request.Position, request.TextDocument);
        return null;
      }
      return CreateHover(symbol, cancellationToken);
    }

    private Hover? GetDiagnosticsHover(DafnyDocument document, Position position) {
      var positionStartingWithOne = new Position(position.Line + 1, position.Character + 1);
      foreach (var node in document.VerificationNodeDiagnostic.Children.OfType<MethodOrSubsetTypeNodeDiagnostic>()) {
        if (node.Range.Contains(positionStartingWithOne)) {
          var implementationNumber = 0;
          var implementations = node.Children.OfType<ImplementationNodeDiagnostic>().ToList();
          var splitCountOffset = 0;
          var totalSplitCount = 0;
          foreach (var implementationNode in implementations) {
            if (!implementationNode.Range.Contains(positionStartingWithOne)) {
              continue;
            }

            if (totalSplitCount == 0) {
              totalSplitCount = implementations.Sum(implementation =>
                implementation.SplitCount);
            }

            var assertionNumber = 0;
            var assertions = implementationNode.Children.OfType<AssertionNodeDiagnostic>().ToList();
            var information = "";
            foreach (var assertionNode in assertions) {
              if (assertionNode.Range.Contains(positionStartingWithOne)) {
                var splitNumber = assertionNode.SplitNumber;
                if (splitNumber >= implementationNode.SplitCount
                    || splitNumber >= implementationNode.AssertionBatchCounts.Count) {
                  logger.Log(LogLevel.Error, $"Assertion is referring to split {splitNumber} in {implementationNode.DisplayName} which does not exist.");
                  return null;
                }

                var batchRef = AddAssertionBatchUrl("batch");
                var assertionBatchTime = implementationNode.AssertionBatchTimes[splitNumber];
                var assertionBatchCount = implementationNode.AssertionBatchCounts[splitNumber];
                if (information == "") {
                  information = $"**{node.DisplayName}** metrics:\n\n";
                }
                var assertionId = assertionBatchCount == 1 ? "" : $" #{assertionNode.AssertionNumber + 1}/{assertionBatchCount}";
                var assertionInfo = $" of {batchRef} #{splitCountOffset + splitNumber + 1}/{totalSplitCount} checked in {assertionBatchTime}ms";

                information += $"assertion{assertionId}{assertionInfo}: *";
                information += assertionNode.StatusVerification switch {
                  VerificationStatus.Verified => "Verified",
                  VerificationStatus.Error => "Might not hold",
                  _ => "Not checked",
                };
                information += assertionNode.StatusCurrent switch {
                  CurrentStatus.Current => "",
                  CurrentStatus.Obsolete => "recently",
                  _ => "recently and verifying..."
                };
                information += "*  \n";
              }

              assertionNumber++;
            }

            if (information != "") {
              return CreateMarkdownHover(information);
            }

            implementationNumber++;
            splitCountOffset += implementationNode.SplitCount;
          }
          // Ok no assertion here. Maybe a method?
          if (node.Position.Line == positionStartingWithOne.Line &&
              node.Filename == document.Uri.GetFileSystemPath()) {
            var information = "**" + node.DisplayName + "** metrics:\n\n";
            var assertionBatch = AddAssertionBatchUrl("assertion batch");
            information +=
              !node.Started ? "_Verification not started yet_"
              : !node.Finished ? $"_Still verifying..._  \n{node.TimeSpent:n0}ms elapsed"
              : (node.AssertionBatchCount == 1
                  ? $"{node.LongestAssertionBatchTime:n0}ms in 1 {assertionBatch}  \n"
                  : $"{node.LongestAssertionBatchTime:n0}ms for the longest {assertionBatch} #{node.LongestAssertionBatchTimeIndex + 1}/{node.AssertionBatchCount}   \n") +
                $"{node.ResourceCount:n0} resource units";
            return CreateMarkdownHover(information);
          }
        }
      }

      return null;
    }

    private static string AddAssertionBatchUrl(string batchReference) {
      return $"[{batchReference}](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-verification-attributes-on-assert-statements)";
    }

    private static Hover CreateMarkdownHover(string information) {
      return new Hover {
        Contents = new MarkedStringsOrMarkupContent(
          new MarkupContent {
            Kind = MarkupKind.Markdown,
            Value = $"{information}"
          }
        )
      };
    }

    private static Hover CreateHover(ILocalizableSymbol symbol, CancellationToken cancellationToken) {
      return new Hover {
        Contents = new MarkedStringsOrMarkupContent(
          new MarkupContent {
            // TODO It appears that setting plaintext/markdown doesn't make a difference, at least in VSCode.
            Kind = MarkupKind.Markdown,
            Value = $"```dafny\n{symbol.GetDetailText(cancellationToken)}\n```"
          }
        )
      };
    }
  }
}
