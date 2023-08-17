using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public interface ISymbolResolver {
    CompilationUnit ResolveSymbols(DafnyProject project, Program program, CancellationToken cancellationToken);
  }
}
