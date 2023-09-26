using System;
using System.Collections.Generic;
using System.Globalization;
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
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.JsonRpc.Server;
using VC;
using EnsuresDescription = Microsoft.Dafny.ProofObligationDescription.EnsuresDescription;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnyHoverHandler : HoverHandlerBase {
    // TODO add the range of the name to the hover.
    private readonly ILogger logger;
    private readonly IProjectDatabase projects;
    private DafnyOptions options;

    private const long RuLimitToBeOverCostly = 10000000;
    private const string OverCostlyMessage =
      " [⚠](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-verification-debugging-slow)";

    public DafnyHoverHandler(ILogger<DafnyHoverHandler> logger, IProjectDatabase projects, DafnyOptions options) {
      this.logger = logger;
      this.projects = projects;
      this.options = options;
    }

    protected override HoverRegistrationOptions CreateRegistrationOptions(HoverCapability capability, ClientCapabilities clientCapabilities) {
      return new HoverRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny")
      };
    }

    public override async Task<Hover?> Handle(HoverParams request, CancellationToken cancellationToken) {
      logger.LogDebug("received hover request for {Document}", request.TextDocument);
      IdeState? state;
      try {
        state = await projects.GetResolvedDocumentAsyncInternal(request.TextDocument);
      } catch (OperationCanceledException) {
        return new Hover {
          Contents = new MarkedStringsOrMarkupContent(new MarkupContent {
            Kind = MarkupKind.Markdown,
            Value = "No hover information available due to program error"
          })
        };
      }
      if (state == null) {
        logger.LogWarning("the document {Document} is not loaded", request.TextDocument);
        return null;
      }
      var diagnosticHoverContent = GetDiagnosticsHover(state, request.TextDocument.Uri.ToUri(), request.Position, out var areMethodStatistics);
      var (symbol, symbolHoverContent) = GetStaticHoverContent(request, state);
      if (diagnosticHoverContent == null && symbolHoverContent == null) {
        return null;
      }

      // If diagnostics are method diagnostics, we prioritize displaying the symbol information.
      // This makes testing easier and less surprise for the user.
      var hoverContent = areMethodStatistics && symbolHoverContent != null && symbol is not MemberDecl ? "" : (diagnosticHoverContent ?? "");
      hoverContent = symbolHoverContent != null ? hoverContent + (hoverContent != "" ? "  \n" : "") + symbolHoverContent : hoverContent;
      return CreateMarkdownHover(hoverContent);
    }

    private (ISymbol? symbol, string? symbolHoverContent) GetStaticHoverContent(HoverParams request, IdeState state) {
      IDeclarationOrUsage? declarationOrUsage =
        state.Program.FindNode<IDeclarationOrUsage>(request.TextDocument.Uri.ToUri(), request.Position.ToDafnyPosition());
      ISymbol? symbol;

      if (declarationOrUsage is IHasUsages usage) {
        symbol = state.SymbolTable.UsageToDeclaration.GetValueOrDefault(usage) as ISymbol;
      } else {
        // If we hover over a usage, display the information of the declaration
        symbol = declarationOrUsage as ISymbol;
        if (symbol != null && !symbol.NameToken.ToRange().ToLspRange().Contains(request.Position)) {
          symbol = null;
        }
      }

      if (symbol == null) {
        logger.LogDebug("no symbol was found at {Position} in {Document}", request.Position, request.TextDocument);
      }

      var symbolHoverContent = symbol != null ? CreateSymbolMarkdown(symbol) : null;
      return (symbol, symbolHoverContent);
    }

    class AssertionBatchIndexComparer : IComparer<AssertionBatchIndex> {
      public int Compare(AssertionBatchIndex? key1, AssertionBatchIndex? key2) {
        return key1 == null || key2 == null ? -1 :
          key1.ImplementationIndex < key2.ImplementationIndex ? -1 :
          key1.ImplementationIndex == key2.ImplementationIndex ? key1.RelativeIndex - key2.RelativeIndex : 1;
      }
    }

    private string? GetDiagnosticsHover(IdeState state, Uri uri, Position position, out bool areMethodStatistics) {
      areMethodStatistics = false;
      var uriDiagnostics = state.GetDiagnosticsForUri(uri).ToList();
      foreach (var diagnostic in uriDiagnostics) {
        if (diagnostic.Range.Contains(position)) {
          string? detail = ErrorRegistry.GetDetail(diagnostic.Code);
          if (detail is not null) {
            return detail;
          }
        }
      }

      return GetVerificationHoverContent(state, uri, position, ref areMethodStatistics, uriDiagnostics);
    }

    private string? GetVerificationHoverContent(IdeState state, Uri uri, Position position, ref bool areMethodStatistics,
      List<Diagnostic> uriDiagnostics) {
      if (uriDiagnostics.Any(diagnostic =>
            diagnostic.Severity == DiagnosticSeverity.Error && (
              diagnostic.Source == MessageSource.Parser.ToString() ||
              diagnostic.Source == MessageSource.Resolver.ToString()))) {
        return null;
      }

      var tree = state.VerificationResults.GetValueOrDefault(uri);
      if (tree == null) {
        return null;
      }

      foreach (var (verifiableRange, result) in tree) {
        if (!verifiableRange.Contains(position)) {
          continue;
        }

        var assertionBatches = result.Implementations.Values.SelectMany(implView => implView.Results).ToList();
        var assertionBatchCount = assertionBatches.Count;
        var information = "";
        var orderedAssertionBatches =
          assertionBatches;
        // .OrderBy(keyValue => keyValue.Key)
        // .Select(keyValuePair => keyValuePair.Value)
        // .ToList();

        foreach (var assertionBatch in orderedAssertionBatches) {
          int batchIndex = assertionBatch.vcNum;
          var assertRanges = assertionBatch.asserts.Select(assert => Translator.ToDafnyToken(assert.tok).ToRange()).ToList();
          var minPosition = assertRanges.Select(r => r.StartToken.GetLspPosition()).Min() ?? verifiableRange.Start;
          var maxPosition = assertRanges.Select(r => r.EndToken.GetLspPosition()).Max() ?? verifiableRange.End;
          var assertionRange = new Range(minPosition, maxPosition);
          if (!assertionRange.Contains(position)) {
            continue;
          }

          assertionBatch.ComputePerAssertOutcomes(out var perAssertOutcome, out var perAssertCounterExample);

          var assertionIndex = 0;
          var assertions = assertionBatch.asserts;
          foreach (var assertion in assertions) {
            var assertRange = Translator.ToDafnyToken(assertion.tok).ToRange().ToLspRange();

            Counterexample? counterexample = perAssertCounterExample.GetValueOrDefault(assertion);
            var assertionRelatedRanges = GetAssertionRelatedRanges(assertion, counterexample);
            if (assertRange.Contains(position) ||
                assertionRelatedRanges.Any(range => range.Contains(position))) {
              if (information != "") {
                information += "\n\n";
              }

              information += GetAssertionInformation(state, position, batchIndex, assertionBatch,
                assertion, counterexample, assertionBatchCount, perAssertOutcome[assertion]);
            }

            assertionIndex++;
          }
        }

        if (information != "") {
          return information;
        }

        // Ok no assertion here. Maybe a method?
        if (verifiableRange.Start.Line == position.Line) {
          areMethodStatistics = true;
          return GetTopLevelInformation(result);
        }
      }

      return null;
    }

    private List<Range> GetAssertionRelatedRanges(AssertCmd assertion, Counterexample? counterexample) {

      var tok = assertion.tok;
      var result = new List<Range>();
      while (tok is NestedToken nestedToken) {
        tok = nestedToken.Inner;
        if (tok.filename == assertion.tok.filename) {
          result.Add(tok.GetLspRange());
        }
      }

      if (counterexample is ReturnCounterexample returnCounterexample) {
        tok = returnCounterexample.FailingReturn.tok;
        if (tok.filename == assertion.tok.filename) {
          result.Add(returnCounterexample.FailingReturn.tok.GetLspRange());
        }
      }

      return result;
    }

    private string GetTopLevelInformation(IdeVerificationResult verificationResult) {
      var vcResults = verificationResult.Implementations.Values.SelectMany(r => r.Results).ToList();
      int assertionBatchCount = vcResults.Count;
      var information = $"**Verification performance metrics for {node.PrefixedDisplayName}**:\n\n";
      if (!node.Started) {
        information += "_Verification not started yet_  \n";
      } else if (!node.Finished) {
        information += "_Still verifying..._  \n";
      }

      var assertionBatchesToReport =
        vcResults.OrderByDescending(a => a.resourceCount).Take(3).ToList();
      if (assertionBatchesToReport.Count == 0 && node.Finished) {
        information += "No assertions.";
      } else if (assertionBatchesToReport.Count >= 1) {
        var totalResourceCount = vcResults.Sum(r => r.resourceCount);
        information += $"- Total resource usage: {FormatResourceCount(totalResourceCount)}";
        if (totalResourceCount > RuLimitToBeOverCostly) {
          information += OverCostlyMessage;
        }

        information += "  \n";
        if (vcResults.Count == 1) {
          var assertionBatch = AddAssertionBatchDocumentation("assertion batch");
          var numberOfAssertions = vcResults.First().asserts.Count();
          information +=
            $"- Only one {assertionBatch} containing {numberOfAssertions} assertion{(numberOfAssertions == 1 ? "" : "s")}.";
        } else {
          var assertionBatches = AddAssertionBatchDocumentation("assertion batches");
          information += $"- Most costly {assertionBatches}:";
          var result =
            new List<(string index, string line, string numberOfAssertions, string assertionPlural, string
              resourceCount, bool overCostly)>();
          foreach (var costlierAssertionBatch in assertionBatchesToReport) {
            var item = costlierAssertionBatch.Range.Start.Line + 1;
            var overCostly = costlierAssertionBatch.resourceCount > RuLimitToBeOverCostly;
            result.Add(("#" + costlierAssertionBatch.vcNum, item.ToString(),
              costlierAssertionBatch.asserts.Count + "",
              costlierAssertionBatch.asserts.Count != 1 ? "s" : "",
              FormatResourceCount(costlierAssertionBatch.resourceCount), overCostly));
          }

          var maxIndexLength = result.Select(item => item.index.Length).Max();
          var maxLineLength = result.Select(item => item.line.Length).Max();
          var maxNumberOfAssertionsLength = result.Select(item => item.numberOfAssertions.Length).Max();
          var maxAssertionsPluralLength = result.Select(item => item.assertionPlural.Length).Max();
          var maxResourceLength = result.Select(item => item.resourceCount.Length).Max();
          foreach (var (index, line, numberOfAssertions, assertionPlural, resource, overCostly) in result) {
            information +=
              $"  \n  - {index.PadLeft(maxIndexLength)}/{assertionBatchCount}" +
              $" with {numberOfAssertions.PadLeft(maxNumberOfAssertionsLength)} assertion" +
              assertionPlural.PadRight(maxAssertionsPluralLength) +
              $" at line {line.PadLeft(maxLineLength)}, {resource.PadLeft(maxResourceLength)}";
            if (overCostly) {
              information += OverCostlyMessage;
            }
          }
        }
      }

      return information;
    }

    private string GetAssertionInformation(IdeState ideState, Position position, int batchIndex,
      VCResult vcResult, AssertCmd assertion, Counterexample? counterexample, int assertionBatchCount, ProverInterface.Outcome outcome) {
      var batchRef = AddAssertionBatchDocumentation("batch");
      var assertionCount = vcResult.asserts.Count;

      var currentlyHoveringPostcondition =
        counterexample is ReturnCounterexample returnCounterexample2 &&
          !returnCounterexample2.FailingReturn.tok.GetLspRange().Contains(position);

      var obsolescence = assertionNode.StatusCurrent switch {
        CurrentStatus.Current => "",
        CurrentStatus.Obsolete => "(obsolete) ",
        _ => "(verifying) "
      };

      string GetDescription(Boogie.ProofObligationDescription? description) {
        switch (assertionNode?.StatusVerification) {
          case GutterVerificationStatus.Verified: {
              var successDescription = description?.SuccessDescription ?? "_no message_";
              return $"{obsolescence}<span style='color:green'>**Success:**</span> " +
                     successDescription;
            }
          case GutterVerificationStatus.Error:
            var failureDescription = description?.FailureDescription ?? "_no message_";
            if (description is EnsuresDescription ensuresDescription) {
              if (currentlyHoveringPostcondition) {
                failureDescription = ensuresDescription.FailureDescriptionSingle;
              } else {
                failureDescription = ensuresDescription.FailureAtPathDescription;
              }
            }
            return $"{obsolescence}[**Error:**](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-verification-debugging) " +
                   failureDescription;
          case GutterVerificationStatus.Inconclusive:
            return $"{obsolescence}**Ignored or could not reach conclusion**";
          default: return $"{obsolescence}**Waiting to be verified...**";
        };
      }

      string information = "";

      string couldProveOrNotPrefix = (vcResult.outcome) switch {
        ProverInterface.Outcome.Valid => "Did prove: ",
        ProverInterface.Outcome.Invalid => "Could not prove: ",
        ProverInterface.Outcome.TimeOut => expr,
        ProverInterface.Outcome.OutOfMemory => expr,
        ProverInterface.Outcome.OutOfResource => expr,
        ProverInterface.Outcome.Undetermined => "Not able to prove: ",
        ProverInterface.Outcome.Bounded => expr,
        _ => throw new ArgumentOutOfRangeException()
      };


      string couldProveOrNotPrefix = (assertionNode.StatusVerification) switch {
        GutterVerificationStatus.Verified => "Did prove: ",
        GutterVerificationStatus.Error => "Could not prove: ",
        GutterVerificationStatus.Inconclusive => "Not able to prove: ",
        _ => "Unknown: "
      };

      string MoreInformation(Boogie.IToken? token, bool hoveringPostcondition) {
        string deltaInformation = "";
        while (token != null) {
          var errorToken = token;
          if (token is NestedToken nestedToken) {
            errorToken = nestedToken.Outer;
            token = nestedToken.Inner;
          } else {
            token = null;
          }

          // It's not necessary to restate the postcondition itself if the user is already hovering it
          // however, nested postconditions should be displayed
          if (errorToken is BoogieRangeToken rangeToken && !hoveringPostcondition) {
            var originalText = rangeToken.PrintOriginal();
            deltaInformation += "  \n" + (token == null ? couldProveOrNotPrefix : "Inside ") + "`" + originalText + "`";
          }

          hoveringPostcondition = false;
        }

        return deltaInformation;
      }

      if (counterexample is ReturnCounterexample returnCounterexample) {
        if (assertionNode.StatusVerification == GutterVerificationStatus.Error &&
            returnCounterexample.FailingEnsures.Description.SuccessDescription != "assertion always holds") {
          // Specialization for ensures marked with {:error} attribute
          // Note that GetDescription checks if user is hovering postcondition
          // so if there is no {:error}, it falls back to a correct error message
          information += GetDescription(returnCounterexample.FailingEnsures.Description);
        } else {
          information += GetDescription(returnCounterexample.FailingReturn.Description);
        }
        information += MoreInformation(returnCounterexample.FailingAssert.tok, currentlyHoveringPostcondition);
      } else if (counterexample is CallCounterexample callCounterexample) {
        if (assertionNode.StatusVerification == GutterVerificationStatus.Error &&
            callCounterexample.FailingRequires.Description.SuccessDescription != "assertion always holds"
            ) {
          // Specialization for requires marked with {:error} attribute
          information += GetDescription(callCounterexample.FailingRequires.Description);
        } else {
          information += GetDescription(callCounterexample.FailingCall.Description);
        }
        information += MoreInformation(callCounterexample.FailingRequires.tok, false);
      } else if (assertCmd is AssertRequiresCmd assertRequiresCmd) {
        information += GetDescription(assertRequiresCmd.Description);
        information += MoreInformation(assertRequiresCmd.Requires.tok, currentlyHoveringPostcondition);
      } else if (assertCmd is AssertEnsuresCmd assertEnsuresCmd) {
        information += GetDescription(assertEnsuresCmd.Description);
        information += MoreInformation(assertEnsuresCmd.Ensures.tok, currentlyHoveringPostcondition);
      } else {
        information += GetDescription(assertCmd?.Description);
        if (assertCmd?.tok is NestedToken) {
          information += MoreInformation(assertCmd.tok, currentlyHoveringPostcondition);
        }
      }

      information += "  \n";
      information += "This is " + (assertionCount == 1
        ? "the only assertion"
        : $"assertion #{assertionIndex + 1} of {assertionCount}");
      if (assertionBatchCount > 1) {
        information += $" in {batchRef} #{batchIndex} of {assertionBatchCount}";
      }

      information += " in " + node.PrefixedDisplayName + "  \n";
      if (assertionBatchCount > 1) {
        information += AddAssertionBatchDocumentation("Batch") +
                       $" #{batchIndex} resource usage: " +
                       FormatResourceCount(vcResult.resourceCount);
      } else {
        information += "Resource usage: " +
                       FormatResourceCount(vcResult.resourceCount);
      }

      var filePath = Translator.ToDafnyToken(assertCmd.tok).Filepath;

      IToken? secondaryToken = Translator.ToDafnyToken(counterexample is ReturnCounterexample returnCounterexample3 ? returnCounterexample3.FailingReturn.tok :
        counterexample is CallCounterexample callCounterexample3 ? callCounterexample3.FailingRequires.tok :
        null);
      var secondaryPosition = secondaryToken?.GetLspPosition();

      // Not the main error displayed in diagnostics
      if (currentlyHoveringPostcondition) {
        information += "  \n" + (secondaryPosition != null
          ? $"Return path: {Path.GetFileName(filePath)}({secondaryPosition.Line + 1}, {secondaryPosition.Character + 1})"
          : "");
      }

      if (counterexample is CallCounterexample) {
        information += "  \n" + (secondaryPosition != null
          ? $"Failing precondition: {Path.GetFileName(filePath)}({secondaryPosition.Line + 1}, {secondaryPosition.Character + 1})"
          : "");
      }

      return information;
    }

    private static readonly int SignificativeDigits = 3;

    public static long RoundToSignificativeDigits(long nodeResourceCount) {
      var nDigits = ("" + nodeResourceCount).Length;
      if (nDigits > SignificativeDigits) {
        var toRemove = (long)Math.Pow(10, nDigits - SignificativeDigits);
        nodeResourceCount += toRemove / 2;
        nodeResourceCount -= (nodeResourceCount % toRemove);
      }

      return nodeResourceCount;
    }

    public static string FormatResourceCount(long nodeResourceCount) {
      var suffix = 0;
      var fractional = 0;
      nodeResourceCount = RoundToSignificativeDigits(nodeResourceCount);

      while (nodeResourceCount / 1000 >= 1 && suffix < 4) {
        fractional = (int)(nodeResourceCount % 1000);
        nodeResourceCount /= 1000;
        suffix += 1; // We don't go past 4 because no suffix beyond T should be useful
      }
      var nfi = new NumberFormatInfo() {
        NumberDecimalDigits = 0,
        NumberGroupSeparator = "",
      };
      var nodeResourceCountStr = nodeResourceCount.ToString(nfi);
      var fractionalStr = nodeResourceCountStr.Length >= SignificativeDigits || suffix == 0 ?
        "" :
        "." + $"{fractional:000}".Remove(SignificativeDigits - nodeResourceCountStr.Length);
      var letterSuffix = suffix switch {
        0 => "",
        1 => "K",
        2 => "M",
        3 => "G",
        _ => "T"
      };
      return $"{nodeResourceCountStr}{fractionalStr}{letterSuffix} RU";
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

    private string CreateSymbolMarkdown(ISymbol symbol) {
      var docString = symbol is IHasDocstring nodeWithDocstring ? nodeWithDocstring.GetDocstring(options) : "";
      return (docString + $"\n```dafny\n{symbol.GetDescription(options)}\n```").TrimStart();
    }
  }
}
