using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Contains a string value and a range
/// Why not just store an IToken and use the value from there instead of storing a separate string?
/// Because generated names don't have an associated token
/// </summary>
public class Name : RangeNode {

  public Name Prepend(string prefix) {
    return new Name(Origin.MakeAutoGenerated(), prefix + Value);
  }

  public Name Append(string suffix) {
    return new Name(Origin, Value + suffix);
  }

  public Name Update(Func<string, string> update) {
    return new Name(Origin, update(Value));
  }
  public string Value { get; set; }

  public Name(Cloner cloner, Name original) : base(cloner, original) {
    Value = original.Value;
  }

  [SyntaxConstructor]
  public Name(IOrigin origin, string value) : base(origin) {
    this.Value = value;
  }

  public Name(IOrigin token) : this(token, token.val) {
  }

  public Name(string value) : base(SourceOrigin.NoToken) {
    this.Value = value;
  }

  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => Children;

  public Name Clone(Cloner cloner) {
    return new Name(cloner.Origin(Origin), Value);
  }

  public override string ToString() => Value;
}