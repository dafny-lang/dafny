using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnySignatureHelpHandler(
    ILogger<DafnySignatureHelpHandler> logger,
    IProjectDatabase projects,
    ISymbolGuesser symbolGuesser,
    DafnyOptions options)
    : SignatureHelpHandlerBase {
    // TODO this is a very basic implementation that only displays the signature when typing an opening parenthese.
    //      It should be enriched to show information about the actual parameter depending on the cursor's position.
    private readonly ILogger logger = logger;

    protected override SignatureHelpRegistrationOptions CreateRegistrationOptions(SignatureHelpCapability capability, ClientCapabilities clientCapabilities) {
      return new SignatureHelpRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny"),
        TriggerCharacters = new Container<string>("(")
      };
    }

    public override async Task<SignatureHelp?> Handle(SignatureHelpParams request, CancellationToken cancellationToken) {
      logger.LogDebug("received signature request for document {DocumentUri}", request.TextDocument.Uri);
      var state = await projects.GetResolvedDocumentAsyncInternal(request.TextDocument);
      if (state == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return null;
      }
      return new SignatureHelpProcessor(logger, symbolGuesser, state, request, cancellationToken, options).Process();
    }

    private class SignatureHelpProcessor(
      ILogger logger,
      ISymbolGuesser symbolGuesser,
      IdeState state,
      SignatureHelpParams request,
      CancellationToken cancellationToken,
      DafnyOptions options) {
      public SignatureHelp? Process() {
        if (!symbolGuesser.TryGetSymbolBefore(state,
              request.TextDocument.Uri.ToUri(), GetOpenParenthesisPosition(), cancellationToken, out var symbol)) {
          logger.LogDebug($"Could not find signature help for {request.TextDocument.Uri}, version {state.Version}");
          return null;
        }
        return CreateSignatureHelp(symbol);
      }

      private Position GetOpenParenthesisPosition() {
        return new Position(request.Position.Line, request.Position.Character - 1);
      }

      private SignatureHelp? CreateSignatureHelp(ILegacySymbol symbol) {
        var signatureInformation = symbol switch {
          MethodSymbol method => CreateSignatureInformation(method),
          FunctionSymbol function => CreateSignatureInformation(function),
          _ => null
        };
        if (signatureInformation == null) {
          return null;
        }
        return new SignatureHelp {
          Signatures = new[] { signatureInformation }
        };
      }

      private SignatureInformation CreateSignatureInformation(ILocalizableSymbol symbol) {
        return new SignatureInformation {
          Label = symbol.Name,
          Documentation = new MarkupContent {
            Kind = MarkupKind.Markdown,
            Value = $"```dafny\n{symbol.GetDetailText(options, cancellationToken)}\n```"
          },
        };
      }
    }
  }
}
