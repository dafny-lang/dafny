using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ExportSignature : TokenNode, IHasReferences {
  public readonly IOrigin ClassIdTok;
  public readonly bool Opaque;
  public readonly string ClassId;
  public readonly string Id;

  [FilledInDuringResolution] public Declaration Decl;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Tok != null);
    Contract.Invariant(Id != null);
    Contract.Invariant((ClassId != null) == (ClassIdTok != null));
  }

  public ExportSignature(IOrigin prefixTok, string prefix, IOrigin idTok, string id, bool opaque) {
    Contract.Requires(prefixTok != null);
    Contract.Requires(prefix != null);
    Contract.Requires(idTok != null);
    Contract.Requires(id != null);
    tok = idTok;
    ClassIdTok = prefixTok;
    ClassId = prefix;
    Id = id;
    Opaque = opaque;
    OwnedTokensCache = new List<IOrigin>() { Tok, prefixTok };
  }

  public ExportSignature(IOrigin idTok, string id, bool opaque) {
    Contract.Requires(idTok != null);
    Contract.Requires(id != null);
    tok = idTok;
    Id = id;
    Opaque = opaque;
    OwnedTokensCache = new List<IOrigin>() { Tok };
  }

  public ExportSignature(Cloner cloner, ExportSignature original) {
    tok = cloner.Origin(original.Tok);
    Id = original.Id;
    Opaque = original.Opaque;
    ClassId = original.ClassId;
    ClassIdTok = cloner.Origin(original.ClassIdTok);
    OwnedTokensCache = new List<IOrigin>() { Tok };
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
    return new[] { new Reference(Tok, Decl) };
  }
}