package DafnyClasses;

import java.math.BigInteger;

// Dafny bytes are default unsigned, whereas they are signed in Java, and there is no unsigned equivalent
public class DafnyULong {
    private long inner;
    public final static long MAXVALUE = 0xffffffffffffffffl;
    public final static BigInteger MAXBI = new BigInteger("18446744073709551615");

    public DafnyULong(byte by) {
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedLong(by);
    }

    public DafnyULong(short sh) {
        //simply casting to an int will preserve the sign
        inner = Short.toUnsignedLong(sh);
    }

    public DafnyULong(DafnyULong other){
        inner = other.inner;
    }

    public DafnyULong(int i) {
        inner = Integer.toUnsignedLong(i);
    }

    public DafnyULong(long l) {
        inner = l;
    }

    public DafnyULong(BigInteger b) {
        assert b.compareTo(MAXBI) <= 0 : "Precondition Failure";
        inner = b.longValue() < 0 ? 0xffffffffffffffffl + MAXBI.subtract(b).longValue(): b.longValue();
    }

    public long value() {
        return inner;
    }

    public static int compare(DafnyULong x, DafnyULong y) {
        return x.compareTo(y);
    }

    public int compareTo(DafnyULong other) {
        return Long.compareUnsigned(inner, other.inner);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public DafnyULong add(DafnyULong other) {
        assert asBigInteger().add(other.asBigInteger()).compareTo(MAXBI) <= 0 : "Precondition Failure";
        return new DafnyULong(inner + other.inner);
    }

    //Invariant that other.inner is positive, so no overflow check needed
    public DafnyULong subtract(DafnyULong other) {
        assert asBigInteger().subtract(other.asBigInteger()).compareTo(BigInteger.ZERO) >= 0 : "Precondition Failure";
        return new DafnyULong(inner - other.inner);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public DafnyULong multiply(DafnyULong other) {
        assert asBigInteger().multiply(other.asBigInteger()).compareTo(MAXBI) <= 0 : "Precondition Failure";
        return new DafnyULong(inner * other.inner);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public DafnyULong divide(DafnyULong other) {
        assert other.inner != 0 : "Precondition Failure";
        return new DafnyULong(Long.divideUnsigned(inner, other.inner));
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public DafnyULong mod(DafnyULong other) {
        assert other.inner != 0 : "Precondition Failure";
        return new DafnyULong(Long.remainderUnsigned(inner, other.inner));
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        DafnyULong o = (DafnyULong) obj;
        return inner == o.inner;
    }

    @Override
    public int hashCode() {
        return Long.hashCode(inner);
    }

    @Override
    public String toString() {
        return Long.toString(inner);
    }

    private BigInteger asBigInteger() {
        return new BigInteger(Long.toUnsignedString(inner));
    }
}
