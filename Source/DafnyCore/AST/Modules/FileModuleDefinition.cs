using System.Collections.Generic;

namespace Microsoft.Dafny;

/// <summary>
/// This is a temporary container of everything declared at the top level of a file, including include directives.
/// After parsing, the contents of this 'module' are moved into the default module.
/// In the future, files may declare implicit modules and then this class will play a non-temporary role:
/// https://github.com/dafny-lang/dafny/issues/3027
/// </summary>
public class FileModuleDefinition : ModuleDefinition {
  public List<Include> Includes { get; } = new();

  public FileModuleDefinition(IToken token) :
    base(token.ToRange(), new Name("_module"), new List<IToken>(),
      false, false, null, null, null, true) {
    {
    }
  }

  public FileModuleDefinition(Cloner cloner, FileModuleDefinition original)
    : base(cloner, original) {
    Includes = original.Includes;
  }
}