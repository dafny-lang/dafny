package dafny;

import java.math.BigInteger;

// Dafny bytes are default unsigned, whereas they are signed in Java, and there is no unsigned equivalent.
// This class uses a `long` to hold the 64 bits that would go into a `ulong`.
public class ULong {
    private long inner;
    public final static BigInteger ULONG_LIMIT = new BigInteger("18446744073709551616");  // 0x1_0000_0000_0000_0000

    // interpret the 8 bits of `by` as an unsigned quantity
    public ULong(byte by) {
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedLong(by);
    }

    // interpret the 16 bits of `sh` as an unsigned quantity
    public ULong(short sh) {
        //simply casting to an int will preserve the sign
        inner = Short.toUnsignedLong(sh);
    }

    public ULong(ULong other){
        inner = other.inner;
    }

    public ULong(dafny.UInt other){
        this(other.value());
    }

    public ULong(dafny.UShort other){
        this(other.value());
    }

    public ULong(dafny.UByte other){
        this(other.value());
    }

    // interpret the 32 bits of `i` as an unsigned quantity
    public ULong(int i) {
        inner = Integer.toUnsignedLong(i);
    }

    // interpret the 64 bits of `l` as an unsigned quantity
    public ULong(long l) {
        // but remember, that's how we're storing `inner`, so no conversion is needed
        inner = l;
    }

    public ULong(BigInteger b) {
        assert b.compareTo(BigInteger.ZERO) >= 0 && b.compareTo(ULONG_LIMIT) < 0 : "Precondition Failure";
        // b.longValue() takes the low-order 64 bits of b and crams them into a long.
        // If bit 63 is set, then inner, as a long, will be negative, but this is what
        // we want, since we're only using inner as storage for 64 bits.
        inner = b.longValue();
    }

    public ULong() {
        inner = 0L;
    }

    // return the 64 bits of the ULong, effectively casting this to a signed 64-bit quantity
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
        assert asBigInteger().add(other.asBigInteger()).compareTo(ULONG_LIMIT) < 0 : "Precondition Failure";
        return new ULong(inner + other.inner);
    }

    //Invariant that other.inner is positive, so no overflow check needed
    public ULong subtract(ULong other) {
        assert asBigInteger().subtract(other.asBigInteger()).compareTo(BigInteger.ZERO) >= 0 : "Precondition Failure";
        return new ULong(inner - other.inner);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public ULong multiply(ULong other) {
        assert asBigInteger().multiply(other.asBigInteger()).compareTo(ULONG_LIMIT) < 0 : "Precondition Failure";
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

    public BigInteger asBigInteger() {
        if (0 <= inner) {
            return BigInteger.valueOf(inner);
        } else {
            return BigInteger.valueOf(inner).add(ULONG_LIMIT);
        }
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
        return new ULong(inner >>> i);
    }
}
