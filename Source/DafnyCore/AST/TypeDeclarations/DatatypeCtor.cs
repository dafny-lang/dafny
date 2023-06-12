using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class DatatypeCtor : Declaration, TypeParameter.ParentType, IHasDocstring {
  public readonly bool IsGhost;
  public readonly List<Formal> Formals;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Formals));
    Contract.Invariant(Destructors != null);
    Contract.Invariant(
      Destructors.Count == 0 || // this is until resolution
      Destructors.Count == Formals.Count);  // after resolution
  }

  public override IEnumerable<Node> Children => base.Children.Concat(Formals);

  // TODO: One could imagine having a precondition on datatype constructors
  [FilledInDuringResolution] public DatatypeDecl EnclosingDatatype;
  [FilledInDuringResolution] public SpecialField QueryField;
  [FilledInDuringResolution] public List<DatatypeDestructor> Destructors = new List<DatatypeDestructor>();  // includes both implicit (not mentionable in source) and explicit destructors

  public DatatypeCtor(RangeToken rangeToken, Name name, bool isGhost, [Captured] List<Formal> formals, Attributes attributes)
    : base(rangeToken, name, attributes, false) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(formals));
    this.Formals = formals;
    this.IsGhost = isGhost;
  }

  public string FullName {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(EnclosingDatatype != null);

      return "#" + EnclosingDatatype.FullName + "." + Name;
    }
  }

  protected override string GetTriviaContainingDocstring() {
    if (EndToken.TrailingTrivia.Trim() != "") {
      return EndToken.TrailingTrivia;
    }

    return GetTriviaContainingDocstringFromStartTokenOrNull();
  }
}