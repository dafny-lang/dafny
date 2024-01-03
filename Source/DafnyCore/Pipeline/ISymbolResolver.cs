using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny {
  public interface ISymbolResolver {
    void ResolveSymbols(Compilation compilation, Program program, CancellationToken cancellationToken);
  }
}
