using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public interface ISymbolResolver {
    void ResolveSymbols(DafnyProject project, Program program, CancellationToken cancellationToken);
  }
}
