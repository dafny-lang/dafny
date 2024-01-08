package Library;

import dafny.*;
import java.math.*;

// The Java compiler doesn't support Dafny methods in extern libraries
public class LibClass {
    // static method CallMeInt(x: int) returns (y: int, z: int)
    public static Tuple2 CallMeInt(BigInteger x) {
      BigInteger y = x.add(BigInteger.ONE);
      BigInteger z = y.add(y);
      return new Tuple2<>(y, z);
    }
    // static method CallMeNative(x: MyInt, b: bool) returns (y: MyInt)
    public static int CallMeNative(int x, boolean b) {
      int y = b ? x + 1 : x - 1;
      return y;
    }
  }