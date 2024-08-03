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

  public Name Append(string suffix) {
    return new Name(RangeToken, Value + suffix);
  }

  public Name Update(Func<string, string> update) {
    return new Name(RangeToken, update(Value));
  }
  public string Value { get; set; }

  public Name(ICloner cloner, Name original) : base(cloner, original) {
    Value = original.Value;
  }

  public Name(RangeToken range, string value) : base(range) {
    this.Value = value;
  }

  public Name(IToken token) : this(new RangeToken(token, token), token.val) {
  }

  public Name(string value) : base(RangeToken.NoToken) {
    this.Value = value;
  }

  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => Children;

  public Name Clone(ICloner cloner) {
    return new Name(cloner.Tok(RangeToken), Value);
  }

  public override string ToString() => Value;
}

public interface ICloner {
  RangeToken Tok(RangeToken rangeToken);
}