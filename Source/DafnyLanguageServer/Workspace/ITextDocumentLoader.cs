using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations are responsible to load a specified language server document and generate
  /// a dafny document out of it.
  /// </summary>
  public interface ITextDocumentLoader {

    Task<Program> ParseAsync(Compilation compilation, CancellationToken cancellationToken);

    Task<ResolutionResult> ResolveAsync(CompilationInput input,
      Program program,
      CancellationToken cancellationToken);
  }
}
