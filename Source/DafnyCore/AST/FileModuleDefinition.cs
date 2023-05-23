using System.Collections.Generic;

namespace Microsoft.Dafny;

public class FileModuleDefinition : ModuleDefinition {
  public List<Include> Includes { get; } = new();

  public FileModuleDefinition() :
    base(RangeToken.NoToken, new Name("_module"), new List<IToken>(),
      false, false, null, null, null, true) {
    {
    }
  }

  public override bool IsDefaultModule => true;
}