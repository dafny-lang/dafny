using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class NonglobalVariable : TokenNode, IVariable {
  readonly string name;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(name != null);
    Contract.Invariant(type != null);
  }

  public string Name {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return name;
    }
  }
  public string DafnyName => RangeToken == null || tok.line == 0 ? Name : RangeToken.PrintOriginal();
  public string DisplayName =>
    LocalVariable.DisplayNameHelper(this);

  private string uniqueName;
  public string UniqueName => uniqueName;
  public bool HasBeenAssignedUniqueName => uniqueName != null;
  public string AssignUniqueName(FreshIdGenerator generator) {
    return uniqueName ??= generator.FreshId(Name + "#");
  }

  static char[] specialChars = { '\'', '_', '?', '\\', '#' };
  /// <summary>
  /// Mangle name <c>nm</c> by replacing and escaping characters most likely to cause issues when compiling and
  /// when translating to Boogie.  This transformation is injective.
  /// </summary>
  /// <returns>A string uniquely determined from <c>nm</c>, containing none of the characters in
  /// <c>specialChars</c>.</returns>
  public static string SanitizeName(string nm) {
    if ('0' <= nm[0] && nm[0] <= '9') {
      // the identifier is one that consists of just digits
      return "_" + nm;
    }
    string name = null;
    int i = 0;
    while (true) {
      int j = nm.IndexOfAny(specialChars, i);
      if (j == -1) {
        if (i == 0) {
          return nm;  // this is the common case
        } else {
          return name + nm.Substring(i);
        }
      } else {
        string nxt = nm.Substring(i, j - i);
        name = name == null ? nxt : name + nxt;
        switch (nm[j]) {
          case '\'': name += "_k"; break;
          case '_': name += "__"; break;
          case '?': name += "_q"; break;
          case '\\': name += "_b"; break;
          case '#': name += "_h"; break;
          default:
            Contract.Assume(false);  // unexpected character
            break;
        }
        i = j + 1;
        if (i == nm.Length) {
          return name;
        }
      }
    }
  }

  private string sanitizedName;
  public virtual string SanitizedName =>
    sanitizedName ??= $"_{IVariable.CompileNameIdGenerator.FreshNumericId()}_{SanitizeName(Name)}";

  protected string compileName;
  public virtual string CompileName =>
    compileName ??= SanitizedName;

  Type type;
  public bool IsTypeExplicit = false;
  public Type SyntacticType { get { return type; } }  // returns the non-normalized type
  public PreType PreType { get; set; }

  public Type Type {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);
      return type.Normalize();
    }
  }

  /// <summary>
  /// For a description of the difference between .Type and .UnnormalizedType, see Expression.UnnormalizedType.
  /// </summary>
  public Type UnnormalizedType {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);
      return type;
    }
  }
  Type IVariable.OptionalType {
    get { return Type; }  // same as Type for NonglobalVariable
  }
  public abstract bool IsMutable {
    get;
  }
  bool isGhost;  // readonly after resolution
  public bool IsGhost {
    get {
      return isGhost;
    }
    set {
      isGhost = value;
    }
  }
  public void MakeGhost() {
    IsGhost = true;
  }

  public NonglobalVariable(IToken tok, string name, Type type, bool isGhost) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(type != null);
    this.tok = tok;
    this.name = name;
    this.type = type;
    this.isGhost = isGhost;
  }

  public IToken NameToken => tok;
  public override IEnumerable<INode> Children => IsTypeExplicit ? new List<Node> { Type } : Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => IsTypeExplicit ? new List<Node>() { Type } : Enumerable.Empty<Node>();
  public DafnySymbolKind Kind => DafnySymbolKind.Variable;
  public string GetDescription(DafnyOptions options) {
    return this.AsText();
  }
}