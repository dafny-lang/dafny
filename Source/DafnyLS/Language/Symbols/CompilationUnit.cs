using System.Collections.Generic;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// A compilation unit represents the outermost scope/symbol of a document.
  /// </summary>
  internal class CompilationUnit : Symbol {
    public ISet<ModuleSymbol> Modules { get; } = new HashSet<ModuleSymbol>();

    public override IEnumerable<Symbol> Children => Modules;

    public CompilationUnit(Microsoft.Dafny.Program program) : base(null, program.Name) {
    }
  }
}
