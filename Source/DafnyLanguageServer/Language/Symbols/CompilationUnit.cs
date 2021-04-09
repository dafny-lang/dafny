using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// A compilation unit represents the outermost scope/symbol of a document.
  /// </summary>
  public class CompilationUnit : Symbol {
    public Dafny.Program Program { get; }

    public ISet<ModuleSymbol> Modules { get; } = new HashSet<ModuleSymbol>();

    public override IEnumerable<ISymbol> Children => Modules;

    public CompilationUnit(Dafny.Program program) : base(null, program.Name) {
      Program = program;
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}
