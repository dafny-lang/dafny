using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public interface IDocumentEntry {
  Task<DafnyDocument> ResolvedDocument { get; }
  Task<DafnyDocument> TranslatedDocument { get; }
  DafnyDocument LastPublishedDocument { get; }
  Task<DafnyDocument> LastDocument { get; }
  public bool Idle { get; }
  void MarkVerificationStarted();

  void MarkVerificationFinished();

}