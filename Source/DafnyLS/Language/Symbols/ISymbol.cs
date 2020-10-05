using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyLS.Language.Symbols {
  internal interface ISymbol {
    DocumentSymbol AsLspSymbol();
  }
}
