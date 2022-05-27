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

/// <summary>
/// A verification quick fixers provides quick "fixes" for verification errors.
/// For now, it offers to inline a failing postcondition if there is no "return" keyword.
/// </summary>
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

    var expression = QuickFixerHelpers.Extract(relatedInformation.Location.Range, input.Code);
    var (beforeEndBrace, indentationExtra, indentationUntilBrace) =
      QuickFixerHelpers.GetInformationToInsertAtEndOfBlock(input, diagnostic.Range.Start);
    if (beforeEndBrace == null) {
      return null;
    }

    return new QuickFix[] {
      new InstantQuickFix(
        "Make the failing assertion explicit",
        new[] {
          new QuickFixEdit(beforeEndBrace,
            $"{indentationExtra}assert {expression};\n{indentationUntilBrace}")
        }
      )
    };

  }
}