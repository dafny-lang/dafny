using System;
using System.IO;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
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

    public override async Task<Hover?> Handle(HoverParams request, CancellationToken cancellationToken) {
      logger.LogTrace("received hover request for {Document}", request.TextDocument);
      var document = await documents.GetDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("the document {Document} is not loaded", request.TextDocument);
        return null;
      }
      var diagnosticHoverContent = GetDiagnosticsHover(document, request.Position);
      if (!document.SymbolTable.TryGetSymbolAt(request.Position, out var symbol)) {
        logger.LogDebug("no symbol was found at {Position} in {Document}", request.Position, request.TextDocument);
      }

      var symbolHoverContent = symbol != null ? CreateSymbolMarkdown(symbol, cancellationToken) : null;
      if (diagnosticHoverContent == null && symbolHoverContent == null) {
        return null;
      }

      var hoverContent = diagnosticHoverContent == null ? "" : diagnosticHoverContent;
      hoverContent += symbolHoverContent == null ? (hoverContent != "" ? "  \n" : "") : symbolHoverContent;
      return CreateMarkdownHover(hoverContent);
    }

    private string? GetDiagnosticsHover(DafnyDocument document, Position position) {
      foreach (var node in document.VerificationTree.Children.OfType<TopLevelDeclMemberVerificationTree>()) {
        if (node.Range.Contains(position)) {
          var assertionBatchCount = node.AssertionBatchCount;
          var assertionBatchIndex = -1;
          var information = "";
          foreach (var assertionBatch in node.AssertionBatches) {
            assertionBatchIndex += 1;
            if (!assertionBatch.Range.Contains(position)) {
              continue;
            }

            var assertionIndex = 0;
            var assertions = assertionBatch.Children.OfType<AssertionVerificationTree>().ToList();
            foreach (var assertionNode in assertions) {
              if (assertionNode.Range.Contains(position) ||
                  assertionNode.ImmediatelyRelatedRanges.Any(range => range.Contains(position))) {
                var assertCmd = assertionNode.GetAssertion();
                var batchRef = AddAssertionBatchDocumentation("batch");
                var assertionBatchTime = assertionBatch.TimeSpent;
                var assertionBatchResourceCount = assertionBatch.ResourceCount;
                var assertionCount = assertionBatch.Children.Count;

                var assertionId = assertionCount == 1 ? "" : $" #{assertionIndex + 1}/{assertionCount}";
                var assertionInfo = $" of {batchRef} #{assertionBatchIndex + 1}/{assertionBatchCount} checked in {assertionBatchTime:n0}ms with {assertionBatchResourceCount:n0} resource count";

                information += $"assertion{assertionId}{assertionInfo}:  \n";
                // Not the main error displayed in diagnostics
                if (!(assertionNode.GetCounterExample() is ReturnCounterexample returnCounterexample2 &&
                      returnCounterexample2.FailingReturn.tok.GetLspRange().Contains(position))) {
                  information += assertionNode.SecondaryPosition != null
                    ? $"`{Path.GetFileName(assertionNode.Filename)}({assertionNode.SecondaryPosition.Line + 1}, {assertionNode.SecondaryPosition.Character + 1}): `"
                    : "";
                }

                information += "*";
                var statusMessage = assertionNode.StatusVerification switch {
                  VerificationStatus.Verified => "Verified",
                  VerificationStatus.Inconclusive => "Could not be checked",
                  VerificationStatus.Error => assertCmd?.ErrorMessage ?? "Might not hold",
                  _ => "Not checked",
                };
                var counterexample = assertionNode.GetCounterExample();

                void SetDescription(ProofObligationDescription? description) {
                  if (description == null) {
                    return;
                  }

                  statusMessage = assertionNode?.StatusVerification switch {
                    VerificationStatus.Verified => description.SuccessDescription,
                    VerificationStatus.Error => description.FailureDescription,
                    _ => statusMessage
                  };
                }

                if (counterexample is ReturnCounterexample returnCounterexample) {
                  SetDescription(returnCounterexample.FailingReturn.Description);
                } else if (counterexample is CallCounterexample callCounterexample) {
                  SetDescription(callCounterexample.FailingCall.Description);
                }

                information += statusMessage;
                information += assertionNode.StatusCurrent switch {
                  CurrentStatus.Current => "",
                  CurrentStatus.Obsolete => "recently",
                  _ => "recently and verifying..."
                };
                information += "*  \n";
              }

              assertionIndex++;
            }
          }

          if (information != "") {
            return information;
          }
          // Ok no assertion here. Maybe a method?
          if (node.Position.Line == position.Line &&
              node.Filename == document.Uri.GetFileSystemPath()) {
            information = "**" + node.DisplayName + "** metrics:\n\n";
            var assertionBatch = AddAssertionBatchDocumentation("assertion batch");
            var firstAssert = node.GetLongestAssertionBatch()?.Children[0];
            var lineFirstAssert = firstAssert == null ? "" : " at line " + (firstAssert.Position.Line + 1);
            information +=
              !node.Started ? "_Verification not started yet_"
              : !node.Finished ? $"_Still verifying..._  \n{node.TimeSpent:n0}ms elapsed"
              : (node.AssertionBatchCount == 1
                  ? $"{node.LongestAssertionBatchTime:n0}ms in 1 {assertionBatch}  \n"
                  : $"{node.LongestAssertionBatchTime:n0}ms for the longest {assertionBatch} #{node.LongestAssertionBatchTimeIndex + 1}/{node.AssertionBatchCount}{lineFirstAssert}   \n") +
                $"{node.ResourceCount:n0} resource count";
            return information;
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
            Value = information
          }
        )
      };
    }

    private static string CreateSymbolMarkdown(ILocalizableSymbol symbol, CancellationToken cancellationToken) {
      return $"```dafny\n{symbol.GetDetailText(cancellationToken)}\n```";
    }
  }
}
