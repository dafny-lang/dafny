package Arrays;

import java.math.BigInteger;

public class __default {
  public static <T> Arrays.Array<T> NewArray(dafny.TypeDescriptor<T> type, BigInteger length) {
    dafny.Array<T> wrapped = dafny.Array.newArray(type, length.intValue());
    return new Arrays.JavaArray<T>(wrapped, length.intValue());
  }
}
