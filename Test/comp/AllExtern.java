package Library;

import java.math.BigInteger;

public class AllExtern {
    public static void P() {
        System.out.println("AllExtern.P");
    }
    public static Wrappers_Compile.Option<BigInteger> MaybeInt() {
        return Wrappers_Compile.Option.create_Some(BigInteger.valueOf(42));
    }
    public static Wrappers_Compile.Pair<BigInteger, BigInteger> IntPair() {
        return Wrappers_Compile.Pair.create_Pair(BigInteger.valueOf(3), BigInteger.valueOf(7));
    }
}