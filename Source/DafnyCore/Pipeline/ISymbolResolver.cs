using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny {
  public interface ISymbolResolver {
    Task ResolveSymbols(Compilation compilation, Program program, CancellationToken cancellationToken);
  }
}
