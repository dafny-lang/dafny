package dafny;

import java.math.BigInteger;

public class BigOrdinal {
    public static boolean IsLimit(BigInteger b){
        return b.equals(BigInteger.ZERO);
    }

    public static boolean IsSucc(BigInteger b){
        return b.compareTo(BigInteger.ZERO) > 0;
    }

    public static BigInteger Offset(BigInteger b){
        return b;
    }

    public static boolean IsNat(BigInteger b){
        return true; //at runtime every ORDINAL is a natural number
    }
}
