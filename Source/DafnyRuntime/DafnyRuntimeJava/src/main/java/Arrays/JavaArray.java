package Arrays;

import java.math.BigInteger;

public class JavaArray<T> implements Arrays.Array<T>, ImmutableArray<T> {
  private final dafny.Array<T> wrapped;
  private final int length;
  
  JavaArray(dafny.Array<T> wrapped, int length) {
    this.wrapped = wrapped;
    this.length = length;
  }

  @Override
  public BigInteger Length() {
    return BigInteger.valueOf(wrapped.length());
  }

  @Override
  public T At(BigInteger index) {
    return Read(index);
  }

  @Override
  public ImmutableArray<T> Slice(BigInteger start, BigInteger end) {
    dafny.Array<T> newArray = wrapped.copyOfRange(start.intValue(), end.intValue());
    return new JavaArray<T>(newArray, end.intValue() - start.intValue());
  }

  @Override
  public T Read(BigInteger i) {
    return wrapped.get(i.intValue());
  }

  @Override
  public void Write(BigInteger i, T t) {
    wrapped.set(i.intValue(), t);
  }

  @Override
  public void WriteRangeArray(BigInteger start, ImmutableArray<T> other) {
    JavaArray<T> otherJavaArray = (JavaArray<T>)other;
    int length = other.Length().intValue();
    int startInt = start.intValue();
    for (int i = 0; i < length; i++) {
      wrapped.set(startInt + i, otherJavaArray.wrapped.get(i));
    }
  }

  @Override
  public ImmutableArray<T> Freeze(BigInteger size) {
    int sizeInt = size.intValue();
    if (sizeInt == length) {
      return this;
    } else {
      return new JavaArray<T>(wrapped, sizeInt);
    }
  }
}


