using System.Collections.Generic;
using Microsoft.Dafny;

namespace DafnyCore.Test;

public class AllocateArrayClonerTest {

  /// <summary>
  /// ElementType is the very same object as ExplicitType when the user wrote a type, and the
  /// resolver resolves it in place, so a clone that produced two separate objects left
  /// ExplicitType unresolved in an otherwise fully resolved AST -- reachable from surface Dafny
  /// through the refinement clone of a method body (git-issue-6345c.dfy), where it crashed
  /// MatchFlattener. Deriving ElementType makes that unrepresentable, and this pins it: the
  /// crash is also absorbed by the null guard in the UserDefinedType clone constructor, so no
  /// .dfy test can tell whether the slots agree.
  /// </summary>
  [Fact]
  public void CloningKeepsElementTypeAliasedToExplicitType() {
    var origin = new Token();
    var original = new AllocateArray(origin, new UserDefinedType(origin, "C", null),
      new List<Expression> { new LiteralExpr(origin, 10) }, null);
    Assert.Same(original.ExplicitType, original.ElementType);

    var clone = original.Clone(new Cloner());

    Assert.NotSame(original.ExplicitType, clone.ExplicitType);
    Assert.Same(clone.ExplicitType, clone.ElementType);
  }

  /// <summary>
  /// Without an explicit type there is nothing to derive from: ElementType is a proxy of its own,
  /// and it must stay one rather than becoming a cloned ExplicitType.
  /// </summary>
  [Fact]
  public void CloningWithoutAnExplicitTypeKeepsTheElementTypeProxy() {
    var origin = new Token();
    var original = new AllocateArray(origin, null,
      new List<Expression> { new LiteralExpr(origin, 10) }, null);
    Assert.Null(original.ExplicitType);
    Assert.IsType<InferredTypeProxy>(original.ElementType);

    var clone = original.Clone(new Cloner());

    Assert.Null(clone.ExplicitType);
    Assert.IsType<InferredTypeProxy>(clone.ElementType);
  }
}
