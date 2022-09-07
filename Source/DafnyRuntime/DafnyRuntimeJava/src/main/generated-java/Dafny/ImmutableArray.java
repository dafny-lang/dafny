// Interface ImmutableArray
// Dafny trait ImmutableArray compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public interface ImmutableArray<T> {
  public java.math.BigInteger Length();
  public T Select(java.math.BigInteger index);
  public ImmutableArray<T> Subarray(java.math.BigInteger lo, java.math.BigInteger hi);
}
