package dafny;

import java.math.BigInteger;

// Dafny bytes are default unsigned, whereas they are signed in Java, and there is no unsigned equivalent
public class ULong {
    private long inner;
    public final static long MAXVALUE = 0xffffffffffffffffl;
    public final static BigInteger MAXBI = new BigInteger("18446744073709551615");

    public ULong(byte by) {
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedLong(by);
    }

    public ULong(short sh) {
        //simply casting to an int will preserve the sign
        inner = Short.toUnsignedLong(sh);
    }

    public ULong(ULong other){
        inner = other.inner;
    }

    public ULong(int i) {
        inner = Integer.toUnsignedLong(i);
    }

    public ULong(long l) {
        inner = l;
    }

    public ULong(BigInteger b) {
        assert b.compareTo(MAXBI) <= 0 : "Precondition Failure";
        inner = b.longValue() < 0 ? 0xffffffffffffffffl + MAXBI.subtract(b).longValue(): b.longValue();
    }

    public ULong(){
        inner = 0L;
    }

    public long value() {
        return inner;
    }

    public static int compare(ULong x, ULong y) {
        return x.compareTo(y);
    }

    public int compareTo(ULong other) {
        return Long.compareUnsigned(inner, other.inner);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public ULong add(ULong other) {
        assert asBigInteger().add(other.asBigInteger()).compareTo(MAXBI) <= 0 : "Precondition Failure";
        return new ULong(inner + other.inner);
    }

    //Invariant that other.inner is positive, so no overflow check needed
    public ULong subtract(ULong other) {
        assert asBigInteger().subtract(other.asBigInteger()).compareTo(BigInteger.ZERO) >= 0 : "Precondition Failure";
        return new ULong(inner - other.inner);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public ULong multiply(ULong other) {
        assert asBigInteger().multiply(other.asBigInteger()).compareTo(MAXBI) <= 0 : "Precondition Failure";
        return new ULong(inner * other.inner);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public ULong divide(ULong other) {
        assert other.inner != 0 : "Precondition Failure";
        return new ULong(Long.divideUnsigned(inner, other.inner));
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public ULong mod(ULong other) {
        assert other.inner != 0 : "Precondition Failure";
        return new ULong(Long.remainderUnsigned(inner, other.inner));
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        ULong o = (ULong) obj;
        return inner == o.inner;
    }

    @Override
    public int hashCode() {
        return Long.hashCode(inner);
    }

    @Override
    public String toString() {
        return Long.toUnsignedString(inner);
    }

    private BigInteger asBigInteger() {
        return new BigInteger(Long.toUnsignedString(inner));
    }

    public ULong xor(ULong other){
        return new ULong(inner ^ other.inner);
    }

    public ULong or(ULong other){
        return new ULong(inner | other.inner);
    }

    public ULong and(ULong other){
        return new ULong(inner & other.inner);
    }

    public ULong not(){
        return new ULong(~inner);
    }

    public ULong shiftLeft(int i){
        return new ULong(inner << i);
    }

    public ULong shiftRight(int i){
        return new ULong(inner >> i);
    }
}
