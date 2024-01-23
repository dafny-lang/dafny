using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny {
  /// <summary>
  /// Implementations are responsible to load a specified language server document and generate
  /// a dafny document out of it.
  /// </summary>
  public interface ITextDocumentLoader {

    Task<Program> ParseAsync(Compilation compilation, CancellationToken cancellationToken);

    Task<ResolutionResult> ResolveAsync(Compilation compilation,
      Program program,
      CancellationToken cancellationToken);
  }
}
