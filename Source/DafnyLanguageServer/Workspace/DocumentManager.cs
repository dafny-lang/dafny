using System;
using System.Threading.Tasks;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public interface IProjectManager {
  void UpdateDocument(DidChangeTextDocumentParams documentChange);
  void Save(TextDocumentIdentifier documentId);
  Task CloseAsync(TextDocumentIdentifier documentId);
  
  Compilation Compilation { get; }
  Task<IdeState?> GetSnapshotAfterResolutionAsync(TextDocumentIdentifier documentId);
  Task<DocumentAfterParsing?> GetLastDocumentAsync();
  void OpenDocument(DocumentTextBuffer document);
}

class ExplicitProject : ProjectManager {
  public ExplicitProject(IServiceProvider services, ProjectFile profileFile) {
    throw new NotImplementedException();
  }
}

/// <summary>
/// Handles operation on a single document.
/// Handles migration of previously published document state
/// </summary>
public class ImplicitProject : ProjectManager {
}
