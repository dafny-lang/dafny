using OmniSharp.Extensions.LanguageServer.Protocol;
using System.IO;

namespace Microsoft.Dafny.LanguageServer.Util {
  /// <summary>
  /// Extension methods for interacting with documents of the language server protocol.
  /// </summary>
  public static class LspDocumentExtensions {
    /// <summary>
    /// Gets the underlying filename behind the given document URI.
    /// </summary>
    /// <param name="documentUri">The URI of the document to get the filename of.</param>
    /// <returns>The filename of the document represented by the URI.</returns>
    public static string GetFileName(this DocumentUri documentUri) {
      return Path.GetFileName(documentUri.GetFileSystemPath());
    }
  }
}
