// Interface Array
// Dafny trait Array compiled into Java
package Dafny;


@SuppressWarnings({"unchecked", "deprecation"})
public interface Array<T> extends Validatable {
  public java.math.BigInteger Length();
  public T Read(java.math.BigInteger i);
  public void Write(java.math.BigInteger i, T t);
  public void WriteRangeArray(java.math.BigInteger start, ImmutableArray<T> other);
  public ImmutableArray<T> Freeze(java.math.BigInteger size);
}
