using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.Plugins;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language;

class VerificationQuickFixer : DiagnosticQuickFixer {
  protected override IEnumerable<QuickFix>? GetQuickFixes(IQuickFixInput input, Diagnostic diagnostic, Range selection) {
    var uri = input.Uri;
    if (diagnostic.Source != MessageSource.Verifier.ToString()) {
      return null;
    }

    if (diagnostic.RelatedInformation?.FirstOrDefault() is not { } relatedInformation) {
      return null;
    }

    if (relatedInformation.Location.Uri != uri) {
      return null;
    }

    var relatedRange = relatedInformation.Location.Range;
    var expression = QuickFixerHelpers.Extract(relatedRange, input.Code);
    var startToken = diagnostic.Range.Start.ToBoogieToken(input.Code);
    var endToken = QuickFixerHelpers.GetMatchingEndToken(input.Program!, uri, startToken);
    if (endToken == null) {
      return null;
    }

    var (extraIndentation, indentationUntilBrace) = QuickFixerHelpers.GetIndentationBefore(endToken, startToken, input.Code);
    var beforeClosingBrace = endToken.GetLspRange().GetStartRange();
    return new QuickFix[] {
      new InstantQuickFix(
        "Explicit the failing assert",
        new[] {
          new QuickFixEdit(beforeClosingBrace,
            $"{extraIndentation}assert {expression};\n{indentationUntilBrace}")
        }
      )
    };

  }
}