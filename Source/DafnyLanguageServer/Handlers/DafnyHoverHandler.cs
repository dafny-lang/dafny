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
          var implementations = node.Children.OfType<ImplementationNodeDiagnostic>().ToList();
          var assertionBatchCount = node.AssertionBatchCount;
          var assertionBatchIndex = 0;
          foreach (var assertionBatch in node.AssertionBatches) {
            if (!assertionBatch.Range.Contains(positionStartingWithOne)) {
              continue;
            }

            var assertionIndex = 0;
            var assertions = assertionBatch.Children.OfType<AssertionNodeDiagnostic>().ToList();
            var information = "";
            foreach (var assertionNode in assertions) {
              if (assertionNode.Range.Contains(positionStartingWithOne)) {
                var batchRef = AddAssertionBatchDocumentation("batch");
                var assertionBatchTime = assertionBatch.TimeSpent;
                var assertionCount = assertionBatch.Children.Count;
                if (information == "") {
                  information = $"**{node.DisplayName}** metrics:\n\n";
                }
                var assertionId = assertionCount == 1 ? "" : $" #{assertionIndex + 1}/{assertionCount}";
                var assertionInfo = $" of {batchRef} #{assertionBatchIndex + 1}/{assertionBatchCount} checked in {assertionBatchTime}ms";

                information += $"assertion{assertionId}{assertionInfo}: *";
                information += assertionNode.StatusVerification switch {
                  VerificationStatus.Verified => "Verified",
                  VerificationStatus.Inconclusive => "Could not be checked",
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

              assertionIndex++;
            }

            if (information != "") {
              return CreateMarkdownHover(information);
            }

            assertionBatchIndex++;
          }
          // Ok no assertion here. Maybe a method?
          if (node.Position.Line == positionStartingWithOne.Line &&
              node.Filename == document.Uri.GetFileSystemPath()) {
            var information = "**" + node.DisplayName + "** metrics:\n\n";
            var assertionBatch = AddAssertionBatchDocumentation("assertion batch");
            var firstAssert = node.LongestAssertionBatch?.Children[0];
            var lineFirstAssert = firstAssert == null ? "" : " at line " + firstAssert.Position.Line;
            information +=
              !node.Started ? "_Verification not started yet_"
              : !node.Finished ? $"_Still verifying..._  \n{node.TimeSpent:n0}ms elapsed"
              : (node.AssertionBatchCount == 1
                  ? $"{node.LongestAssertionBatchTime:n0}ms in 1 {assertionBatch}  \n"
                  : $"{node.LongestAssertionBatchTime:n0}ms for the longest {assertionBatch} #{node.LongestAssertionBatchTimeIndex + 1}/{node.AssertionBatchCount}{lineFirstAssert}   \n") +
                $"{node.ResourceCount:n0} resource units";
            return CreateMarkdownHover(information);
          }
        }
      }

      return null;
    }

    private static string AddAssertionBatchDocumentation(string batchReference) {
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
