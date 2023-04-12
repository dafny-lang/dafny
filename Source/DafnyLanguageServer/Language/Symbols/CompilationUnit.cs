using System;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// A compilation unit represents the outermost scope/symbol of a document.
  /// </summary>
  public class CompilationUnit : Symbol {
    public Uri EntryDocument { get; }
    public Dafny.Program Program { get; }

    public bool IsPartOfEntryDocument(Boogie.IToken token) {
      // The token filename happens to be null if it's representing a default module or class.
      return token.filename == null || token.filename == EntryDocument.LocalPath;
    }
    
    public ISet<ModuleSymbol> Modules { get; } = new HashSet<ModuleSymbol>();

    public override IEnumerable<ISymbol> Children => Modules;

    public CompilationUnit(Uri entryDocument, Dafny.Program program) : base(null, program.Name) {
      EntryDocument = entryDocument;
      Program = program;
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
