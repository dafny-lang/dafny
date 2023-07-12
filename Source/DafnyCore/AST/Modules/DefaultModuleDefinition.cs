using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class DefaultModuleDefinition : ModuleDefinition, ICloneable<DefaultModuleDefinition> {
  public List<Include> Includes { get; } = new();
  public IList<Uri> RootSourceUris { get; }

  public DefaultModuleDefinition(Cloner cloner, DefaultModuleDefinition original) : base(cloner, original, original.NameNode) {
    RootSourceUris = original.RootSourceUris;
  }

  public DefaultModuleDefinition(IList<Uri> rootSourceUris)
    : base(RangeToken.NoToken, new Name("_module"), new List<IToken>(), false, false,
      null, null, null, true) {
    RootSourceUris = rootSourceUris;
  }

  public override bool IsDefaultModule => true;
  public override IEnumerable<Node> PreResolveChildren => Includes.Concat(base.PreResolveChildren);
  public new DefaultModuleDefinition Clone(Cloner cloner) {
    return new DefaultModuleDefinition(cloner, this);
  }
}