using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  /// <summary>
  /// Implementations of this interface are responsible to relocate symbols and diagnostics
  /// to their new positions according to the given <see cref="DidChangeTextDocumentParams"/>.
  /// </summary>
  public interface IRelocator {
    ChangeProcessor GetChangeProcessor(DidChangeTextDocumentParams changes, CancellationToken cancellationToken);
  }
}
