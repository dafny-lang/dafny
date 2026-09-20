using Microsoft.Dafny;

namespace DafnyCore.Test;

public class FieldClonerTest {

  /// <summary>
  /// Field had the same duplicated type slot as AllocateArray: Type was set from ExplicitType at
  /// construction and the two were cloned independently, so every clone left ExplicitType
  /// unresolved while Type went on to be resolved. Nothing reads Field.ExplicitType today, which
  /// is the only reason it never surfaced.
  /// </summary>
  [Fact]
  public void CloningKeepsTypeAliasedToExplicitType() {
    var origin = new Token();
    var original = new Field(origin, new Name("f"), false, new UserDefinedType(origin, "C", null), null);
    Assert.Same(original.ExplicitType, original.Type);

    var clone = new Field(new Cloner(), original);

    Assert.NotSame(original.ExplicitType, clone.ExplicitType);
    Assert.Same(clone.ExplicitType, clone.Type);
  }

  /// <summary>
  /// Without an explicit type there is nothing to alias, and Type must stay a proxy of its own.
  /// </summary>
  [Fact]
  public void CloningWithoutAnExplicitTypeKeepsTheTypeProxy() {
    var origin = new Token();
    var original = new Field(origin, new Name("f"), false, null, null);
    Assert.Null(original.ExplicitType);
    Assert.IsType<InferredTypeProxy>(original.Type);

    var clone = new Field(new Cloner(), original);

    Assert.Null(clone.ExplicitType);
    Assert.IsType<InferredTypeProxy>(clone.Type);
  }
}
