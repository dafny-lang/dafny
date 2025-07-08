package Library;

import java.math.BigInteger;

public class AllExtern {
    public static void P() {
        System.out.println("AllExtern.P");
    }
    public static Wrappers.Option<BigInteger> MaybeInt() {
        return Wrappers.Option.create_Some(dafny.TypeDescriptor.BIG_INTEGER, BigInteger.valueOf(42));
    }
    public static Wrappers.Pair<BigInteger, BigInteger> IntPair() {
        return Wrappers.Pair.create(dafny.TypeDescriptor.BIG_INTEGER, dafny.TypeDescriptor.BIG_INTEGER,
                                            BigInteger.valueOf(3), BigInteger.valueOf(7));
    }
}
