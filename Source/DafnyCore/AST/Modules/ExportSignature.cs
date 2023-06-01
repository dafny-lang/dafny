using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ExportSignature : TokenNode, IHasUsages {
  public readonly IToken ClassIdTok;
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

  public ExportSignature(IToken prefixTok, string prefix, IToken idTok, string id, bool opaque) {
    Contract.Requires(prefixTok != null);
    Contract.Requires(prefix != null);
    Contract.Requires(idTok != null);
    Contract.Requires(id != null);
    tok = idTok;
    ClassIdTok = prefixTok;
    ClassId = prefix;
    Id = id;
    Opaque = opaque;
    OwnedTokensCache = new List<IToken>() { Tok, prefixTok };
  }

  public ExportSignature(IToken idTok, string id, bool opaque) {
    Contract.Requires(idTok != null);
    Contract.Requires(id != null);
    tok = idTok;
    Id = id;
    Opaque = opaque;
    OwnedTokensCache = new List<IToken>() { Tok };
  }

  public override string ToString() {
    if (ClassId != null) {
      return ClassId + "." + Id;
    }
    return Id;
  }

  public IToken NameToken => Tok;
  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();
  public override IEnumerable<Node> PreResolveChildren => Enumerable.Empty<Node>();
  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return new[] { Decl };
  }
}