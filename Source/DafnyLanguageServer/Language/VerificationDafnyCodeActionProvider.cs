using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language;

/// <summary>
/// A verification quick fixers provides quick "fixes" for verification errors.
/// For now, it offers to inline a failing postcondition if its failure is
/// indicated on the '{' -- meaning there is no explicit return.
/// </summary>
class VerificationDafnyCodeActionProvider : DiagnosticDafnyCodeActionProvider {
  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input,
    DafnyDiagnostic diagnostic, Range selection) {
    var uri = input.Uri;
    if (diagnostic.Source != MessageSource.Verifier) {
      return null;
    }

    if (diagnostic.RelatedInformation?.FirstOrDefault() is not { } relatedInformation) {
      return null;
    }

    if (relatedInformation.Token.filename != uri) {
      return null;
    }

    var range = relatedInformation.Token.GetLspRange();
    var expression = input.Extract(range);
    var statement = $"assert {expression};";
    var edit = DafnyCodeActionHelpers.InsertAtEndOfBlock(input, diagnostic.Token.GetLspPosition(), statement);
    if (edit == null) {
      return null;
    }

    return new DafnyCodeAction[] {
      new InstantDafnyCodeAction(
        "Assert postcondition at return location where it fails",
        new List<Diagnostic>(){diagnostic.ToLspDiagnostic()},
        new[] { edit }
      )
    };

  }
}