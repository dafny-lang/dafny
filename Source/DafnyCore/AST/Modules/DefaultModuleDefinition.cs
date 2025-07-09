using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class DefaultModuleDefinition : ModuleDefinition, ICloneable<DefaultModuleDefinition> {
  public List<Include> Includes { get; } = [];

  public DefaultModuleDefinition(Cloner cloner, DefaultModuleDefinition original) : base(cloner, original, original.NameNode) {
  }

  public DefaultModuleDefinition()
    : base(SourceOrigin.NoToken, new Name("_module"), [], ModuleKindEnum.Concrete, false,
      null, null, null) {
  }

  public override bool IsDefaultModule => true;

  public override bool TryToAvoidName => Name == "_module";

  public override IEnumerable<INode> Children => Includes.Concat(base.Children);
  public override IEnumerable<INode> PreResolveChildren => Includes.Concat(base.PreResolveChildren);
  public new DefaultModuleDefinition Clone(Cloner cloner) {
    return new DefaultModuleDefinition(cloner, this);
  }
}