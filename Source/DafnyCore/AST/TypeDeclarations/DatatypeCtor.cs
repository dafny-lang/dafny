using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class DatatypeCtor : Declaration, TypeParameter.ParentType, IHasDocstring, ICanVerify {
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

  public override IEnumerable<INode> Children => base.Children.Concat(Formals);

  // TODO: One could imagine having a precondition on datatype constructors
  [FilledInDuringResolution] public DatatypeDecl EnclosingDatatype;
  [FilledInDuringResolution] public SpecialField QueryField;
  [FilledInDuringResolution] public List<DatatypeDestructor> Destructors = new List<DatatypeDestructor>();  // includes both implicit (not mentionable in source) and explicit destructors

  public DatatypeCtor(IOrigin rangeOrigin, Name name, bool isGhost, [Captured] List<Formal> formals, Attributes attributes)
    : base(rangeOrigin, name, attributes, false) {
    Contract.Requires(rangeOrigin != null);
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

  public string GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }

    var tentativeTrivia = EndToken.TrailingTrivia.Trim();
    if (tentativeTrivia != "") {
      return tentativeTrivia;
    }

    return null;
  }

  public override SymbolKind? Kind => SymbolKind.EnumMember;
  public override string GetDescription(DafnyOptions options) {
    var formals = string.Join(", ", Formals.Select(f => f.AsText()));
    return $"{EnclosingDatatype.Name}.{Name}({formals})";
  }

  public ModuleDefinition ContainingModule => EnclosingDatatype.EnclosingModuleDefinition;
  public bool ShouldVerify => Formals.Any(f => f.DefaultValue != null);
  public string FullDafnyName => FullName;
}