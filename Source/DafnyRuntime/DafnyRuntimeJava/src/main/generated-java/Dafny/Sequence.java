// Interface Sequence
// Dafny trait Sequence compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public interface Sequence<T> {
  public java.math.BigInteger Length();
  public T Select(java.math.BigInteger index);
  public Sequence<T> Drop(java.math.BigInteger lo);
  public Sequence<T> Take(java.math.BigInteger hi);
  public Sequence<T> Subsequence(java.math.BigInteger lo, java.math.BigInteger hi);
  public ImmutableArray<T> ToArray();
}
