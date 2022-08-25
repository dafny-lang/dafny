using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public interface IDocumentEntry {
  Task<Compilation> ResolvedDocument { get; }
  Task<Compilation> TranslatedDocument { get; }
  Compilation LastPublishedDocument { get; }
  Task<Compilation> LastDocument { get; }
  public bool Idle { get; }
  void MarkVerificationStarted();

  void MarkVerificationFinished();

}