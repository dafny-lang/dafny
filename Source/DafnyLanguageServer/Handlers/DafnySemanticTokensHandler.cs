using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language.SemanticTokens;

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnySemanticTokensHandler : SemanticTokensHandlerBase {
    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;

    public DafnySemanticTokensHandler(ILogger<DafnySemanticTokensHandler> logger, IDocumentDatabase documents) {
      this.logger = logger;
      this.documents = documents;
    }

    protected override SemanticTokensRegistrationOptions CreateRegistrationOptions(SemanticTokensCapability capability,
      ClientCapabilities clientCapabilities) {
      return new SemanticTokensRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage("dafny"),
        Legend = new SemanticTokensLegend() { // FIXME adjust depending on client (capability.TokenModifiers / capability.TokenTypes)
          TokenModifiers = new Container<SemanticTokenModifier>(SemanticTokenModifier.Defaults),
          TokenTypes = new Container<SemanticTokenType>(SemanticTokenType.Defaults),
        },
        Full = new SemanticTokensCapabilityRequestFull {
          Delta = true
        },
        Range = true
      };
    }

    private void CollectBasicTokens(DafnySemanticTokensBuilder builder, Dafny.Program program) {
      var tok = program.DefaultModule.RootToken.next;
      while (tok != null) {
        builder.Push("parser", tok);
        tok = tok.next;
      }
    }

    private void CollectSemanticTokens(DafnySemanticTokensBuilder builder, Dafny.Program program) {
      new LspSemanticTokensGeneratingVisitor(builder).Visit(program);
    }

    protected override async Task Tokenize(SemanticTokensBuilder builder, ITextDocumentIdentifierParams identifier,
      CancellationToken cancellationToken) {
      var document = await documents.GetDocumentAsync(identifier.TextDocument);
      if (document == null) {
        logger.LogWarning("Tokens requested for unloaded document {DocumentUri}", identifier.TextDocument.Uri);
        return;
      }

      var dafnyBuilder = new DafnySemanticTokensBuilder(builder);
      CollectBasicTokens(dafnyBuilder, document.Program);
      CollectSemanticTokens(dafnyBuilder, document.Program);
    }

    protected override Task<SemanticTokensDocument> GetSemanticTokensDocument(ITextDocumentIdentifierParams @params, CancellationToken cancellationToken) {
      return Task.FromResult(new SemanticTokensDocument(RegistrationOptions.Legend));
    }
  }
}
