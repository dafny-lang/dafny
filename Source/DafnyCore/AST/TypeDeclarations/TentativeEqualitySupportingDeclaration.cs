using System.Collections.Generic;

namespace Microsoft.Dafny;

public interface ITentativeEqualitySupportingDeclaration {
  public enum ES { NotYetComputed, Never, ConsultTypeArguments }
  public ES EqualitySupport { get; set; }
  public List<TypeParameter> TypeParameters { get; }
  public ModuleDefinition EnclosingModuleDefinition { get; }
}