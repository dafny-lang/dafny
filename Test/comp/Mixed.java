package Library;

import java.math.BigInteger;

public class Mixed extends _ExternBase_Mixed {
    private final BigInteger n;

    public Mixed(BigInteger n) {
        this.n = n;
    }

    public static void P() {
        System.out.println("Mixed.P");
    }
    @Override
    public void IP() {
        System.out.println("Mixed.IP");
    }
    public static BigInteger G() {
        return BigInteger.ONE;
    }
    @Override
    public BigInteger IG() {
        return n;
    }
}