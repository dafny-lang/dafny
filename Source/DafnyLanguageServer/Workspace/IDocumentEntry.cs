using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public interface IDocumentEntry {
  Task<Document> ResolvedDocument { get; }
  Task<Document> TranslatedDocument { get; }
  Document LastPublishedDocument { get; }
  Task<Document> LastDocument { get; }
  public bool Idle { get; }
  void MarkVerificationStarted();

  void MarkVerificationFinished();

}