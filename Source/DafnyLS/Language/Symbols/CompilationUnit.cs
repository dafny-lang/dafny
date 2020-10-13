using System.Collections.Generic;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// A compilation unit represents the outermost scope/symbol of a document.
  /// </summary>
  internal class CompilationUnit : Symbol {
    public ISet<ModuleSymbol> Modules = new HashSet<ModuleSymbol>();

    public CompilationUnit(Microsoft.Dafny.Program program) : base(null, program.Name) {
    }

    public override IEnumerable<Symbol> GetAllDescendantsAndSelf() {
      yield return this;
      foreach(var module in Modules) {
        foreach(var descendant in module.GetAllDescendantsAndSelf()) {
          yield return descendant;
        }
      }
    }
  }
}
