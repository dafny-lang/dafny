#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public abstract class NonglobalVariable : NodeWithOrigin, IVariable {
  public Name NameNode { get; }

  [SyntaxConstructor]
  protected NonglobalVariable(IOrigin? origin, Name nameNode, Type? syntacticType, bool isGhost) : base(origin) {
    NameNode = nameNode;
    SyntacticType = syntacticType;
    IsGhost = isGhost;
  }

  public NonglobalVariable(Cloner cloner, NonglobalVariable original) : base(cloner, original) {
    NameNode = new Name(cloner, original.NameNode);
    SyntacticType = cloner.CloneType(original.SyntacticType);
    IsGhost = original.IsGhost;
    if (cloner.CloneResolvedFields) {
      safeSyntacticType = cloner.CloneType(original.safeSyntacticType);
    }
  }

  public string Name => NameNode.Value;

  public string DafnyName => Origin.line == 0 ? Name : EntireRange.PrintOriginal();
  public string DisplayName =>
    LocalVariable.DisplayNameHelper(this);

  private string? uniqueName;
  public string? UniqueName => uniqueName;
  public bool HasBeenAssignedUniqueName => uniqueName != null;
  public string AssignUniqueName(VerificationIdGenerator generator) {
    return uniqueName ??= generator.FreshId(Name + "#");
  }

  static char[] specialChars = ['\'', '_', '?', '\\', '#'];
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
    string? name = null;
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

  private string? sanitizedNameShadowable;

  public virtual string CompileNameShadowable =>
    sanitizedNameShadowable ??= SanitizeName(Name);

  protected string? compileName;

  public virtual string GetOrCreateCompileName(CodeGenIdGenerator generator) {
    return compileName ??= $"_{generator.FreshNumericId()}_{CompileNameShadowable}";
  }

  public Type? SyntacticType;

  private Type? safeSyntacticType;
  public Type SafeSyntacticType => safeSyntacticType ??= SyntacticType ?? new InferredTypeProxy();

  public bool IsTypeExplicit => SyntacticType != null;

  public Type Type => SafeSyntacticType.Normalize();

  /// <summary>
  /// For a description of the difference between .Type and .UnnormalizedType, see Expression.UnnormalizedType.
  /// </summary>
  public Type UnnormalizedType => SafeSyntacticType;

  public PreType? PreType { get; set; }

  Type IVariable.OptionalType {
    get { return Type; }  // same as Type for NonglobalVariable
  }
  public abstract bool IsMutable {
    get;
  }

  public bool IsGhost { get; set; }

  public void MakeGhost() {
    IsGhost = true;
  }

  public TokenRange NavigationRange => NameNode.ReportingRange;
  public override IEnumerable<INode> Children => IsTypeExplicit ? new List<Node> { Type } : Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => IsTypeExplicit ? new List<Node>() { Type } : Enumerable.Empty<Node>();
  public SymbolKind? Kind => SymbolKind.Variable;
  public string GetDescription(DafnyOptions options) {
    return this.AsText();
  }
}