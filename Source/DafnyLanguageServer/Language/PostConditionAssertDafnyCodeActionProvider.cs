using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language;

/// <summary>
/// A verification quick fixers provides quick "fixes" for verification errors.
/// For now, it offers to inline a failing postcondition if its failure is
/// indicated on the '{' -- meaning there is no explicit return.
/// </summary>
class PostConditionAssertDafnyCodeActionProvider : DiagnosticDafnyCodeActionProvider {
  protected override IEnumerable<DafnyCodeAction>? GetDafnyCodeActions(IDafnyCodeActionInput input,
    Diagnostic diagnostic, Range selection) {
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

    var range = FindTokenRangeFromLspRange(input, relatedInformation.Location.Range, true);
    if (range == null) {
      return null;
    }
    var expression = range.PrintOriginal();
    var statement = $"assert {expression};";
    var edit = DafnyCodeActionHelpers.InsertAtEndOfBlock(input, diagnostic.Range.Start, statement);
    if (edit == null) {
      return null;
    }

    return new DafnyCodeAction[] {
      new InstantDafnyCodeAction(
        "Assert postcondition at return location where it fails",
        new List<Diagnostic>(){diagnostic},
        new[] { edit }
      )
    };

  }

  public PostConditionAssertDafnyCodeActionProvider(ILogger<DafnyCodeActionHandler> logger) : base(logger) {
  }
}