#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class Formal : NonglobalVariable {
  public Attributes? Attributes { get; set; }

  public bool InParam;  // true to in-parameter, false for out-parameter
  public override bool IsMutable => !InParam;
  public bool IsOld;
  public Expression? DefaultValue;
  public bool IsNameOnly;
  public bool IsOlder;
  public string NameForCompilation;

  public Formal(IOrigin origin, string name, Type? type, bool inParam, bool isGhost, Expression? defaultValue,
    Attributes? attributes = null,
    bool isOld = false, bool isNameOnly = false, bool isOlder = false, string? nameForCompilation = null)
    : this(origin, new Name(origin.ReportingRange.StartToken, name), type, inParam, isGhost, defaultValue, attributes,
      isOld, isNameOnly, isOlder, nameForCompilation) {
  }

  [SyntaxConstructor]
  public Formal(IOrigin origin, Name nameNode, Type? syntacticType, bool inParam, bool isGhost, Expression? defaultValue,
    Attributes? attributes = null,
    bool isOld = false, bool isNameOnly = false, bool isOlder = false, string? nameForCompilation = null)
    : base(origin, nameNode, syntacticType, isGhost) {
    Contract.Requires(inParam || defaultValue == null);
    Contract.Requires(!isNameOnly || (inParam && !nameNode.Value.StartsWith("#")));
    InParam = inParam;
    IsOld = isOld;
    DefaultValue = defaultValue;
    Attributes = attributes;
    IsNameOnly = isNameOnly;
    IsOlder = isOlder;
    NameForCompilation = nameForCompilation ?? nameNode.Value;
  }

  public Formal(Cloner cloner, Formal original) : base(cloner, original) {
    InParam = original.InParam;
    IsOld = original.IsOld;
    DefaultValue = cloner.CloneExpr(original.DefaultValue);
    Attributes = cloner.CloneAttributes(original.Attributes);
    IsNameOnly = original.IsNameOnly;
    IsOlder = original.IsOlder;
    NameForCompilation = original.NameForCompilation;
  }

  public bool HasName => !Name.StartsWith("#");

  public override string GetOrCreateCompileName(CodeGenIdGenerator generator) {
    return CompileName;
  }

  public string CompileName => compileName ??= SanitizeName(NameForCompilation);

  public override IEnumerable<INode> Children =>
    (DefaultValue != null ? new List<Node> { DefaultValue } : Enumerable.Empty<Node>()).Concat(base.Children);

  public override IEnumerable<INode> PreResolveChildren => Children;
}

/// <summary>
/// An ImplicitFormal is a parameter that is declared implicitly, in particular the "_k" depth parameter
/// of each extreme lemma (for use in the extreme-method body only, not the specification).
/// </summary>
public class ImplicitFormal : Formal {
  public ImplicitFormal(IOrigin origin, string name, Type type, bool inParam, bool isGhost)
    : base(origin, name, type, inParam, isGhost, null, null) {
  }
}

/// <summary>
/// ThisSurrogate represents the implicit parameter "this". It is used to allow more uniform handling of
/// parameters. A pointer value of a ThisSurrogate object is not important, only the fact that it is
/// a ThisSurrogate is. ThisSurrogate objects are only used in specially marked places in the Dafny
/// implementation.
/// </summary>
public class ThisSurrogate : ImplicitFormal {
  public ThisSurrogate(IOrigin origin, Type type)
    : base(origin, "this", type, true, false) {
  }
}