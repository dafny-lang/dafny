using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer {
  /// <summary>
  /// Extension methods for the use with LINQ expressions.
  /// </summary>
  public static class LinqExtensions {
    /// <summary>
    /// Checks between each entry of an enumerable if a cancellation was requested before continuing.
    /// </summary>
    /// <typeparam name="TEntry">The type of the entires to process within the LINQ expression.</typeparam>
    /// <param name="entries">The entries to process.</param>
    /// <param name="cancellationToken"></param>
    /// <returns>The same entries as the input.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    public static IEnumerable<TEntry> WithCancellation<TEntry>(this IEnumerable<TEntry> entries, CancellationToken cancellationToken) {
      foreach (var entry in entries) {
        cancellationToken.ThrowIfCancellationRequested();
        yield return entry;
      }
    }
  }
}
