using System;
using System.Collections.Generic;
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
using VerificationStatus = Microsoft.Dafny.LanguageServer.Workspace.Notifications.VerificationStatus;

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
      var diagnosticHoverContent = GetDiagnosticsHover(document, request.Position, out var areMethodStatistics);
      if (!document.SymbolTable.TryGetSymbolAt(request.Position, out var symbol)) {
        logger.LogDebug("no symbol was found at {Position} in {Document}", request.Position, request.TextDocument);
      }

      var symbolHoverContent = symbol != null ? CreateSymbolMarkdown(symbol, cancellationToken) : null;
      if (diagnosticHoverContent == null && symbolHoverContent == null) {
        return null;
      }

      // If diagnostics are method diagnostics, we prioritize displaying the symbol information.
      // This makes testing easier and less surprise for the user.
      var hoverContent = areMethodStatistics && symbolHoverContent != null ? "" : (diagnosticHoverContent ?? "");
      hoverContent = symbolHoverContent != null ? hoverContent + (hoverContent != "" ? "  \n" : "") + symbolHoverContent : hoverContent;
      return CreateMarkdownHover(hoverContent);
    }

    class TupleComparer : IComparer<(int, int)> {
      public int Compare((int, int) key1, (int, int) key2) {
        return key1.Item1 < key2.Item1 ? -1 :
          key1.Item1 == key2.Item1 ? key1.Item2 - key2.Item1 : 1;
      }
    }

    private string? GetDiagnosticsHover(DafnyDocument document, Position position, out bool areMethodStatistics) {
      areMethodStatistics = false;
      foreach (var node in document.VerificationTree.Children.OfType<TopLevelDeclMemberVerificationTree>()) {
        if (node.Range.Contains(position)) {
          var assertionBatchCount = node.AssertionBatchCount;
          var information = "";
          var orderedAssertionBatches =
            node.AssertionBatches
              .OrderBy(keyValue => keyValue.Key, new TupleComparer()).Select(keyValuePair => keyValuePair.Value)
              .ToList();
          foreach (var assertionBatch in orderedAssertionBatches) {
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
                var assertionCount = assertionBatch.Children.Count;

                var obsolescence = assertionNode.StatusCurrent switch {
                  CurrentStatus.Current => "",
                  CurrentStatus.Obsolete => "(obsolete) ",
                  _ => "(verifying) "
                };

                string GetDescription(Boogie.ProofObligationDescription? description) {
                  return assertionNode?.StatusVerification switch {
                    VerificationStatus.Verified => $"{obsolescence}<span style='color:green'>**Success:**</span> " +
                                                   (description?.SuccessDescription ?? "_no message_"),
                    VerificationStatus.Error => $"{obsolescence}[Error:](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-verification-debugging) " +
                                                (description?.FailureDescription ?? "_no message_"),
                    VerificationStatus.Inconclusive => $"{obsolescence}**Ignored or could not reach conclusion**",
                    _ => $"{obsolescence}**Waiting to be verified...**",
                  };
                }
                var counterexample = assertionNode.GetCounterExample();

                if (information != "") {
                  information += "\n\n";
                }

                if (counterexample is ReturnCounterexample returnCounterexample) {
                  information += GetDescription(returnCounterexample.FailingReturn.Description);
                } else if (counterexample is CallCounterexample callCounterexample) {
                  information += GetDescription(callCounterexample.FailingCall.Description);
                } else {
                  information += GetDescription(assertCmd?.Description);
                }

                information += "  \n";
                information += "This is " + (assertionCount == 1
                  ? "the only assertion"
                  : $"assertion #{assertionIndex + 1} of {assertionCount}");
                if (assertionBatchCount > 1) {
                  information += $" in {batchRef} #{assertionBatch.RelativeNumber} of {assertionBatchCount}";
                }
                information += " in " + node.PrefixedDisplayName + "  \n";
                if (assertionBatchCount > 1) {
                  information += AddAssertionBatchDocumentation("Batch") +
                                 $" #{assertionBatch.RelativeNumber} resource usage: " +
                                 formatResourceCount(assertionBatch.ResourceCount);
                } else {
                  information += "Resource usage: " +
                                 formatResourceCount(assertionBatch.ResourceCount);
                }

                // Not the main error displayed in diagnostics
                if (!(assertionNode.GetCounterExample() is ReturnCounterexample returnCounterexample2 &&
                      returnCounterexample2.FailingReturn.tok.GetLspRange().Contains(position))) {
                  information += "  \n" + (assertionNode.SecondaryPosition != null
                    ? $"Related location: {Path.GetFileName(assertionNode.Filename)}({assertionNode.SecondaryPosition.Line + 1}, {assertionNode.SecondaryPosition.Character + 1})"
                    : "");
                }
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
            areMethodStatistics = true;
            information = $"**Verification performance metrics for {node.PrefixedDisplayName}**:\n\n";
            if (!node.Started) {
              information += "_Verification not started yet_";
            } else if (!node.Finished) {
              information += "_Still verifying..._";
            }


            var assertionBatchesToReport =
              node.AssertionBatches.Values.OrderByDescending(a => a.ResourceCount).Take(3).ToList();
            if (assertionBatchesToReport.Count == 0) {
              information += "No assertions.";
            } else {
              information += $"- Total resource usage: {formatResourceCount(node.ResourceCount)}  \n";
              if (assertionBatchesToReport.Count == 1) {
                var assertionBatch = AddAssertionBatchDocumentation("assertion batch");
                information += $"- Only one {assertionBatch} containing {orderedAssertionBatches.First().NumberOfAssertions} assertions.";
              } else {
                var assertionBatches = AddAssertionBatchDocumentation("assertion batches");
                information += $"- Most costly {assertionBatches}:";
                var result = new List<(String index, String line, String numberOfAssertions, String assertionPlural, String resourceCount, bool overcostly)>();
                foreach (var costlierAssertionBatch in assertionBatchesToReport) {
                  var item = costlierAssertionBatch.Range.Start.Line + 1;
                  var overcostly = costlierAssertionBatch.ResourceCount > 3 * node.ResourceCount / assertionBatchCount;
                  result.Add(("#" + costlierAssertionBatch.RelativeNumber, item.ToString(), costlierAssertionBatch.Children.Count + "",
                    costlierAssertionBatch.Children.Count != 1 ? "s" : "",
                    formatResourceCount(costlierAssertionBatch.ResourceCount), overcostly));
                }

                var maxIndexLength = result.Select(item => item.index.Length).Max();
                var maxLineLength = result.Select(item => item.line.Length).Max();
                var maxNumberOfAssertionsLength = result.Select(item => item.numberOfAssertions.Length).Max();
                var maxAssertionsPluralLength = result.Select(item => item.assertionPlural.Length).Max();
                var maxResourceLength = result.Select(item => item.resourceCount.Length).Max();
                foreach (var (index, line, numberOfAssertions, assertionPlural, resource, overcostly) in result) {
                  information +=
                    $"  \n  - {index.PadLeft(maxIndexLength)}/{assertionBatchCount}" +
                    $" with {numberOfAssertions.PadLeft(maxNumberOfAssertionsLength)} assertion" +
                    assertionPlural.PadRight(maxAssertionsPluralLength) +
                    $" at line {line.PadLeft(maxLineLength)}, {resource.PadLeft(maxResourceLength)}";
                  if (overcostly) {
                    information +=
                      @" [/!\](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-verification-debugging-slow)";
                  }
                }
              }
            }

            return information;
          }
        }
      }

      return null;
    }

    private string formatResourceCount(int nodeResourceCount) {
      var suffix = 0;
      while (nodeResourceCount / 1000 >= 1 && suffix < 3) {
        nodeResourceCount /= 1000;
        suffix += 1;
      }
      var letterSuffix = suffix switch {
        0 => "",
        1 => "K",
        2 => "G",
        _ => "T"
      };
      return $"{nodeResourceCount:n0}{letterSuffix} RU";
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
