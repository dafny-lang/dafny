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
    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;
    private readonly ISymbolGuesser _symbolGuesser;

    public DafnySignatureHelpHandler(ILogger<DafnySignatureHelpHandler> logger, IDocumentDatabase documents, ISymbolGuesser symbolGuesser) {
      _logger = logger;
      _documents = documents;
      _symbolGuesser = symbolGuesser;
    }

    protected override SignatureHelpRegistrationOptions CreateRegistrationOptions(SignatureHelpCapability capability, ClientCapabilities clientCapabilities) {
      return new SignatureHelpRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny"),
        TriggerCharacters = new Container<string>("(")
      };
    }

    public override Task<SignatureHelp?> Handle(SignatureHelpParams request, CancellationToken cancellationToken) {
      DafnyDocument? document;
      if(!_documents.TryGetDocument(request.TextDocument, out document)) {
        _logger.LogWarning("location requested for unloaded document {}", request.TextDocument.Uri);
        return Task.FromResult<SignatureHelp?>(null);
      }
      return Task.FromResult(new SignatureHelpProcessor(_symbolGuesser, document, request, cancellationToken).Process());
    }

    private class SignatureHelpProcessor {
      private readonly ISymbolGuesser _symbolGuesser;
      private readonly DafnyDocument _document;
      private readonly SignatureHelpParams _request;
      private readonly CancellationToken _cancellationToken;

      public SignatureHelpProcessor(ISymbolGuesser symbolGuesser, DafnyDocument document, SignatureHelpParams request, CancellationToken cancellationToken) {
        _symbolGuesser = symbolGuesser;
        _document = document;
        _request = request;
        _cancellationToken = cancellationToken;
      }

      public SignatureHelp? Process() {
        ISymbol? symbol;
        if(!_symbolGuesser.TryGetSymbolBefore(_document, GetOpenParenthesePosition(), _cancellationToken, out symbol)) {
          return null;
        }
        return CreateSignatureHelp(symbol);
      }

      private Position GetOpenParenthesePosition() {
        return new Position(_request.Position.Line, _request.Position.Character - 1);
      }

      private SignatureHelp? CreateSignatureHelp(ISymbol symbol) {
        var signatureInformation = symbol switch {
          MethodSymbol method => CreateSignatureInformation(method),
          FunctionSymbol function => CreateSignatureInformation(function),
          _ => null
        };
        if(signatureInformation == null) {
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
            Value = $"```dafny\n{symbol.GetDetailText(_cancellationToken)}\n```"
          },
        };
      }
    }
  }
}
