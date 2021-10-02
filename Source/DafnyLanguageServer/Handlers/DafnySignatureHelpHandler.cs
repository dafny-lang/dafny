using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnySignatureHelpHandler : SignatureHelpHandlerBase {
    // TODO this is a very basic implementation that only displays the signature when typing an opening parenthese.
    //      It should be enriched to show information about the actual parameter depending on the cursor's position.
    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;
    private readonly ISymbolGuesser symbolGuesser;

    public DafnySignatureHelpHandler(ILogger<DafnySignatureHelpHandler> logger, IDocumentDatabase documents, ISymbolGuesser symbolGuesser) {
      this.logger = logger;
      this.documents = documents;
      this.symbolGuesser = symbolGuesser;
    }

    protected override SignatureHelpRegistrationOptions CreateRegistrationOptions(SignatureHelpCapability capability, ClientCapabilities clientCapabilities) {
      return new SignatureHelpRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny"),
        TriggerCharacters = new Container<string>("(")
      };
    }

    public async override Task<SignatureHelp?> Handle(SignatureHelpParams request, CancellationToken cancellationToken) {
      var document = await documents.GetDocumentAsync(request.TextDocument);
      if (document == null) {
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return null;
      }
      return new SignatureHelpProcessor(symbolGuesser, document, request, cancellationToken).Process();
    }

    private class SignatureHelpProcessor {
      private readonly ISymbolGuesser symbolGuesser;
      private readonly DafnyDocument document;
      private readonly SignatureHelpParams request;
      private readonly CancellationToken cancellationToken;

      public SignatureHelpProcessor(ISymbolGuesser symbolGuesser, DafnyDocument document, SignatureHelpParams request, CancellationToken cancellationToken) {
        this.symbolGuesser = symbolGuesser;
        this.document = document;
        this.request = request;
        this.cancellationToken = cancellationToken;
      }

      public SignatureHelp? Process() {
        if (!symbolGuesser.TryGetSymbolBefore(document, GetOpenParenthesePosition(), cancellationToken, out var symbol)) {
          return null;
        }
        return CreateSignatureHelp(symbol);
      }

      private Position GetOpenParenthesePosition() {
        return new Position(request.Position.Line, request.Position.Character - 1);
      }

      private SignatureHelp? CreateSignatureHelp(ISymbol symbol) {
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
            Value = $"```dafny\n{symbol.GetDetailText(cancellationToken)}\n```"
          },
        };
      }
    }
  }
}
