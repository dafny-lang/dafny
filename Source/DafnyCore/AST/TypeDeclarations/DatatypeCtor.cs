#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class DatatypeCtor : Declaration, TypeParameter.ParentType, IHasDocstring, ICanVerify {
  public bool IsGhost;
  public List<Formal> Formals;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Cce.NonNullElements(Formals));
    Contract.Invariant(
      Destructors.Count == 0 || // this is until resolution
      Destructors.Count == Formals.Count);  // after resolution
  }

  public override IEnumerable<INode> Children => base.Children.Concat(Formals);

  // TODO: One could imagine having a precondition on datatype constructors
  [FilledInDuringResolution] public DatatypeDecl? EnclosingDatatype;
  [FilledInDuringResolution] public SpecialField? QueryField;
  [FilledInDuringResolution] public List<DatatypeDestructor> Destructors = [];  // includes both implicit (not mentionable in source) and explicit destructors

  public DatatypeCtor(IOrigin origin, Name nameNode, bool isGhost, [Captured] List<Formal> formals, Attributes? attributes)
    : base(origin, nameNode, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(Cce.NonNullElements(formals));
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

  public string? GetTriviaContainingDocstring() {
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
    return $"{EnclosingDatatype!.Name}.{Name}({formals})";
  }

  public ModuleDefinition ContainingModule => EnclosingDatatype!.EnclosingModuleDefinition;
  public bool ShouldVerify => Formals.Any(f => f.DefaultValue != null);
  public string FullDafnyName => FullName;
}