using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ExportSignature : NodeWithOrigin, IHasReferences {
  public IOrigin ClassIdTok;
  public bool Opaque;
  public string ClassId;
  public string Id;

  [FilledInDuringResolution] public Declaration Decl;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Origin != null);
    Contract.Invariant(Id != null);
    Contract.Invariant((ClassId != null) == (ClassIdTok != null));
  }

  public ExportSignature(IOrigin prefixTok, string prefix, IOrigin idOrigin, string id, bool opaque) : base(idOrigin) {
    Contract.Requires(prefixTok != null);
    Contract.Requires(prefix != null);
    Contract.Requires(idOrigin != null);
    Contract.Requires(id != null);
    ClassIdTok = prefixTok;
    ClassId = prefix;
    Id = id;
    Opaque = opaque;
  }

  public ExportSignature(IOrigin idOrigin, string id, bool opaque) : base(idOrigin) {
    Contract.Requires(idOrigin != null);
    Contract.Requires(id != null);
    Id = id;
    Opaque = opaque;
  }

  public ExportSignature(Cloner cloner, ExportSignature original) : base(cloner, original) {
    Id = original.Id;
    Opaque = original.Opaque;
    ClassId = original.ClassId;
    ClassIdTok = cloner.Origin(original.ClassIdTok);
  }

  public override string ToString() {
    if (ClassId != null) {
      return ClassId + "." + Id;
    }
    return Id;
  }

  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => Enumerable.Empty<Node>();
  public IEnumerable<Reference> GetReferences() {
    return new[] { new Reference(ReportingRange, Decl) };
  }
}