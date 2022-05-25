using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.Plugins;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language;

class VerificationQuickFixer : DiagnosticQuickFixer {
  private readonly IDocumentDatabase documents;
  private readonly ILogger<DafnyCodeActionHandler> logger;

  public VerificationQuickFixer(IDocumentDatabase documents, ILogger<DafnyCodeActionHandler> logger) {
    this.documents = documents;
    this.logger = logger;
  }

  protected override IEnumerable<QuickFix>? GetQuickFixes(IQuickFixInput input, Diagnostic diagnostic, Range selection) {
    var uri = input.Uri;
    if (diagnostic.Source == MessageSource.Verifier.ToString()) {
      if (diagnostic.RelatedInformation?.FirstOrDefault() is { } relatedInformation) {
        if (relatedInformation.Location.Uri == uri) {
          var relatedRange = relatedInformation.Location.Range;
          var expression = QuickFixerHelpers.Extract(relatedRange, input.Code);
          var startToken = diagnostic.Range.Start.ToBoogieToken(input.Code);
          var endToken = QuickFixerHelpers.GetMatchingEndToken(input.Program!, uri, startToken);
          if (endToken != null) {
            var (indentation, indentationBrace) = QuickFixerHelpers.GetIndentationBefore(endToken, startToken, input.Code);
            var beforeClosingBrace = endToken.GetLspRange().Start;
            return new QuickFix[] {
              new InstantQuickFix(
                "Explicit the failing assert",
                new[] {
                  new QuickFixEdit(
                    (beforeClosingBrace, beforeClosingBrace),
                    $"{indentation}assert {expression};\n{indentationBrace}")
                }
              )
            };
          }
        }
      }
    }

    return null;
  }
}