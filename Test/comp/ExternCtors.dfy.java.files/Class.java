package Library;

import java.math.BigInteger;

public class Class extends _ExternBase_Class {
    private final BigInteger n;

    public Class(BigInteger n) {
        this.n = n;
    }

    public static void SayHi() {
        System.out.println("Hello!");
    }

    public BigInteger Get() {
        return n;
    }
}