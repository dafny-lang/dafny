using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Contains a string value and a range
/// Why not just store an IToken and use the value from there instead of storing a separate string?
/// Because generated names don't have an associated token
/// </summary>
public class Name : RangeNode {
  public static implicit operator Name(string value) => new( value);
    
  public string Value { get; set; }

  public Name(Cloner cloner, Name original) : base(cloner, original) {
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

  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();

  public Name Clone(Cloner cloner) {
    return new Name(cloner.Tok(RangeToken), Value);
  }

  public override string ToString() => Value;
}