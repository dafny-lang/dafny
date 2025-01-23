using System;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// A compilation unit represents the outermost scope/symbol of a document.
  /// </summary>
  public class CompilationUnit(Uri entryDocument, Dafny.Program program) : Symbol(null, program.Name) {
    public Uri EntryDocument { get; } = entryDocument;
    public Dafny.Program Program { get; } = program;

    public bool IsPartOfEntryDocument(Boogie.IToken token) {
      // The token filename happens to be null if it's representing a default module or class.
      return token.filename == null || (token is IOrigin dafnyToken && dafnyToken.Uri == EntryDocument);
    }

    public ISet<ModuleSymbol> Modules { get; } = new HashSet<ModuleSymbol>();

    public override IEnumerable<ILegacySymbol> Children => Modules;

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
