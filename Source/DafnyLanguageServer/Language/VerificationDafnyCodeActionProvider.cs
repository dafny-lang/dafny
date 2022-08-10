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
class VerificationDafnyCodeActionProvider : DiagnosticDafnyCodeActionProvider {
  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input, Diagnostic diagnostic, Range selection) {
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

    var expression = input.Extract(relatedInformation.Location.Range);
    var (beforeEndBrace, indentationExtra, indentationUntilBrace) =
      DafnyCodeActionHelpers.GetInformationToInsertAtEndOfBlock(input, diagnostic.Range.Start);
    if (beforeEndBrace == null) {
      return null;
    }

    return new DafnyCodeAction[] {
      new InstantDafnyCodeAction(
        "Assert postcondition at return location where it fails",
        new List<Diagnostic>(){diagnostic},
        new[] {
          new DafnyCodeActionEdit(beforeEndBrace,
            $"{indentationExtra}assert {expression};\n{indentationUntilBrace}")
        }
      )
    };

  }
}