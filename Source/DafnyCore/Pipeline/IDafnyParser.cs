using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny {
  /// <summary>
  /// Interface exposing parse methods to generate a syntax tree out of an arbitrary dafny source.
  /// </summary>
  /// <remarks>
  /// Any implementation has to guarantee thread-safety of its public members.
  /// </remarks>
  public interface IDafnyParser {
    Task<ProgramParseResult> Parse(Compilation compilation, CancellationToken cancellationToken);
  }
}
