#nullable enable
using System.Collections.Generic;
using System.Linq;
using VCGeneration;

namespace Microsoft.Dafny;

public static class ErrorReporterExtensions {
  public static void ReportBoogieError(this ErrorReporter reporter, ErrorInformation error, bool useRange = true) {
    var usingSnippets = reporter.Options.Get(DafnyConsolePrinter.ShowSnippets);
    var relatedInformation = new List<DafnyRelatedInformation>();
    foreach (var auxiliaryInformation in error.Aux) {
      if (auxiliaryInformation.Category == RelatedMessageCategory) {
        error.Msg += "\n" + auxiliaryInformation.FullMsg;
      } else if (auxiliaryInformation.Category == RelatedLocationCategory) {
        relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(BoogieGenerator.ToDafnyToken(true, auxiliaryInformation.Tok), auxiliaryInformation.Msg, usingSnippets));
      } else {
        // The execution trace is an additional auxiliary which identifies itself with
        // line=0 and character=0. These positions cause errors when exposing them, Furthermore,
        // the execution trace message appears to not have any interesting information.
        if (auxiliaryInformation.Tok.line > 0) {
          reporter.Info(MessageSource.Verifier, BoogieGenerator.ToDafnyToken(true, auxiliaryInformation.Tok), auxiliaryInformation.Msg);
        }
      }
    }

    if (error.Tok is NestedToken { Inner: var innerToken, Message: var msg }) {
      relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(innerToken, msg, usingSnippets));
    }

    var dafnyToken = BoogieGenerator.ToDafnyToken(useRange, error.Tok);

    var tokens = new[] { dafnyToken }.Concat(relatedInformation.Select(i => i.Token)).ToList();
    IToken previous = tokens.Last();
    foreach (var (inner, outer) in relatedInformation.Zip(tokens).Reverse()) {
      previous = new NestedToken(outer, previous, inner.Message);
    }
    reporter.Message(MessageSource.Verifier, ErrorLevel.Error, null, previous, error.Msg);
  }

  private const string RelatedLocationCategory = "Related location";
  public const string RelatedLocationMessage = RelatedLocationCategory;
  private const string RelatedMessageCategory = "Related message";
  public static readonly string PostConditionFailingMessage = new ProofObligationDescription.EnsuresDescription(null, null).FailureDescription;
  private static string FormatRelated(string related) {
    return $"Could not prove: {related}";
  }

  public static IEnumerable<DafnyRelatedInformation> CreateDiagnosticRelatedInformationFor(IToken token, string? message, bool usingSnippets) {
    var (tokenForMessage, inner, newMessage) = token is NestedToken nestedToken ? (nestedToken.Outer, nestedToken.Inner, nestedToken.Message) : (token, null, null);
    var dafnyToken = BoogieGenerator.ToDafnyToken(true, tokenForMessage);
    if (!usingSnippets && dafnyToken is RangeToken rangeToken) {
      if (message == PostConditionFailingMessage) {
        var postcondition = rangeToken.PrintOriginal();
        message = $"this postcondition might not hold: {postcondition}";
      } else if (message == null || message == RelatedLocationMessage) {
        message = FormatRelated(rangeToken.PrintOriginal());
      }
    }

    yield return new DafnyRelatedInformation(token, message);
    if (inner != null) {
      foreach (var nestedInformation in CreateDiagnosticRelatedInformationFor(inner, newMessage, usingSnippets)) {
        yield return nestedInformation;
      }
    }
  }
}