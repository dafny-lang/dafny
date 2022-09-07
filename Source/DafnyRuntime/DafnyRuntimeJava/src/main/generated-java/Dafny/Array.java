// Interface Array
// Dafny trait Array compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public interface Array<T> extends Validatable {
  public java.math.BigInteger Length();
  public T Select(java.math.BigInteger i);
  public void Update(java.math.BigInteger i, T t);
  public void UpdateSubarray(java.math.BigInteger start, ImmutableArray<T> other);
  public ImmutableArray<T> Freeze(java.math.BigInteger size);
}
