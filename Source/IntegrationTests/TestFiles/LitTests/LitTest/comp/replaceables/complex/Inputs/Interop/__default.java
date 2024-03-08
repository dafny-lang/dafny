


package Interop;

import java.lang.Integer;
import java.math.BigInteger;
import dafny.TypeDescriptor;

public class __default {
  public static Integer IntegerMaxValue() {
    return Integer.MAX_VALUE;
  }
  public static BigInteger Int32ToInt(Integer value) {
    return BigInteger.valueOf(value);
  }
  public static Std.Wrappers.Option<Integer> IntToInt32(BigInteger value) {
    try {
      return Std.Wrappers.Option.create_Some(TypeDescriptor.intWithDefault(0), (Integer)value.intValueExact());
    } catch(ArithmeticException e) {
      return Std.Wrappers.Option.create_None(TypeDescriptor.intWithDefault(0));
    }
  }
}