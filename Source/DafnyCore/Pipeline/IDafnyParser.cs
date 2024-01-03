using System.Threading;

namespace Microsoft.Dafny {
  /// <summary>
  /// Interface exposing parse methods to generate a syntax tree out of an arbitrary dafny source.
  /// </summary>
  /// <remarks>
  /// Any implementation has to guarantee thread-safety of its public members.
  /// </remarks>
  public interface IDafnyParser {
    Program Parse(Compilation compilation, CancellationToken cancellationToken);
  }
}
