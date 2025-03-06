#nullable enable
using System.Collections.Generic;
using System.Linq;
using DafnyCore;
using VCGeneration;

namespace Microsoft.Dafny;

public static class ErrorReporterExtensions {
  public static void ReportBoogieError(this ErrorReporter reporter, ErrorInformation error,
    DafnyModel? counterexampleModel = null, bool useRange = true) {
    var usingSnippets = reporter.Options.Get(Snippets.ShowSnippets);
    var relatedInformation = new List<DafnyRelatedInformation>();
    foreach (var auxiliaryInformation in error.Aux) {
      if (auxiliaryInformation.Category == RelatedMessageCategory || auxiliaryInformation.Category == AssertedExprCategory) {
        error.Msg += "\n" + auxiliaryInformation.FullMsg;
      } else if (auxiliaryInformation.Category == RelatedLocationCategory) {
        var auxiliaryToken = BoogieGenerator.ToDafnyToken(true, auxiliaryInformation.Tok);
        relatedInformation.Add(new DafnyRelatedInformation(auxiliaryToken.GetLocation(), auxiliaryInformation.Msg));
        relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(auxiliaryToken, usingSnippets));
      } else {
        // The execution trace is an additional auxiliary which identifies itself with
        // line=0 and character=0. These positions cause errors when exposing them, Furthermore,
        // the execution trace message appears to not have any interesting information.
        if (auxiliaryInformation.Tok.line > 0) {
          reporter.Info(MessageSource.Verifier, BoogieGenerator.ToDafnyToken(true, auxiliaryInformation.Tok), auxiliaryInformation.Msg);
        }
      }
    }

    if (counterexampleModel != null) {
      error.Msg += "\n" + $"Related counterexample:\n{counterexampleModel}";
    }

    relatedInformation.AddRange(CreateDiagnosticRelatedInformationFor(BoogieGenerator.ToDafnyToken(true, error.Tok), usingSnippets));

    var dafnyToken = BoogieGenerator.ToDafnyToken(useRange, error.Tok);

    var diagnostic = new DafnyDiagnostic(MessageSource.Verifier, null!, dafnyToken.Center, error.Msg,
      ErrorLevel.Error, relatedInformation);
    reporter.MessageCore(diagnostic);
  }

  private const string RelatedLocationCategory = "Related location";
  public const string RelatedLocationMessage = RelatedLocationCategory;
  private const string RelatedMessageCategory = "Related message";
  public const string AssertedExprCategory = "Asserted expression";
  public static readonly string PostConditionFailingMessage = new EnsuresDescription(null, null, null).FailureDescription;
  private static string FormatRelated(string related) {
    return $"Could not prove: {related}";
  }

  public static IEnumerable<DafnyRelatedInformation> CreateDiagnosticRelatedInformationFor(IOrigin token, bool usingSnippets) {
    var innerToken = token;
    while (innerToken is OriginWrapper wrapper) {
      if (innerToken is NestedOrigin nestedOrigin) {
        // Turning this on changes many regression tests, in a way that might be considered good,
        // but it should be turned on in a separate PR
        // There seem to be no LSP tests for this behavior, so turning it off did not affect those.

        // var dafnyToken = BoogieGenerator.ToDafnyToken(true, nestedOrigin.Outer);
        // if (!usingSnippets && dafnyToken.IncludesRange) {
        //   if (message == PostConditionFailingMessage) {
        //     var postcondition = dafnyToken.PrintOriginal();
        //     message = $"this postcondition might not hold: {postcondition}";
        //   } else if (message == null|| message == RelatedLocationMessage*/) {
        //     message = FormatRelated(dafnyToken.PrintOriginal());
        //   }
        // }
        yield return new DafnyRelatedInformation(nestedOrigin.Inner.GetLocation(), nestedOrigin.Message);
        innerToken = nestedOrigin.Inner;
      } else {
        innerToken = wrapper.WrappedToken;
      }
    }
  }
}