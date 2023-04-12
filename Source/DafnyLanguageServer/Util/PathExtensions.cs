using System;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;

namespace Microsoft.Dafny.LanguageServer.Util {
  /// <summary>
  /// Collection of methods related to path operations to ensure that all path operations
  /// are compatible with each other.
  /// </summary>
  public static class PathExtensions {
    /// <summary>
    /// Gets the path of the file represented by the given dafny document. The path returned is
    /// in the standard system format. E.g. C:\data\test.dfy for windows or /home/test.dfy for linux.
    /// </summary>
    /// <param name="document">The document to get the file path of.</param>
    /// <returns>The file path.</returns>
    public static string GetFilePath(this Document document) {
      return GetFilePath(document.Uri);
    }

    /// <summary>
    /// Gets the path of the file represented by the given text document. The path returned is
    /// in the standard system format. E.g. C:\data\test.dfy for windows or /home/test.dfy for linux.
    /// </summary>
    /// <param name="document">The document to get the file path of.</param>
    /// <returns>The file path.</returns>
    public static string GetFilePath(this TextDocumentItem document) {
      return GetFilePath(document.Uri);
    }

    private static string GetFilePath(DocumentUri uri) {
      // GetFileSystemPath() is used since Path resolves to a non-Windows path format on Windows, e.g.:
      // /d:/data/file.dfy
      return uri.GetFileSystemPath();
    }

    /// <summary>
    /// Checks if the given URI is the entrypoint document.
    /// </summary>
    /// <param name="program">The dafny program to check the token against.</param>
    /// <param name="documentUri">The URI to check.</param>
    /// <returns><c>true</c> if the given URI is the entrypoint document of the given program.</returns>
    public static bool IsEntryDocument(this Dafny.Program program, DocumentUri documentUri) {
      return documentUri.ToString() == program.FullName;
    }

    /// <summary>
    /// Gets the document uri for the specified boogie token.
    /// </summary>
    /// <param name="token">The token to get the boogie token from.</param>
    /// <returns>The uri of the document where the token is located.</returns>
    public static DocumentUri GetDocumentUri(this Boogie.IToken token) {
      // TODO have do we determine the effect of commenting this out? What test was covering it?
      // HoverGetsForeignContentAsWell hits it, but there this code doesn't change anything.
      // if (token is IncludeToken includeToken) {
      //   return DocumentUri.FromFileSystemPath(includeToken.Include.CanonicalPath);
      // }

      while (token is RefinementToken refinementToken) {
        token = refinementToken.WrappedToken;
      }

      return DocumentUri.Parse(token.filename);
    }

    /// <summary>
    /// Gets the filename of the document where the given boogie token is located in.
    /// </summary>
    /// <param name="token">The token to get the document filename from.</param>
    /// <returns>The filename (without path) of the document containing the given token.</returns>
    public static string GetDocumentFileName(this Boogie.IToken token) {
      return Path.GetFileName(token.filename);
    }
  }
}
