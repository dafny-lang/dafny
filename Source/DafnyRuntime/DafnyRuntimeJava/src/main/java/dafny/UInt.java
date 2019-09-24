package dafny;

import java.math.BigInteger;

// Dafny bytes are default unsigned, whereas they are signed in Java, and there is no unsigned equivalent
public class UInt {
    private int inner;
    public final static int MAXVALUE = 0xffffffff; // 4294967295
    public UInt(byte by){
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedInt(by);
    }

    public UInt(short sh){
        //simply casting to an int will preserve the sign
        inner = Short.toUnsignedInt(sh);
    }

    public UInt(int i){
        inner = i;
    }

    public UInt(long l){
        assert l <= 0xffffffffl: "Precondition Failure";
        inner = (int) l;
    }

    public UInt(){
        inner = 0;
    }

    public UInt(UInt other){
        inner = other.inner;
    }

    public UInt(dafny.UShort other){
        this(other.value());
    }

    public UInt(dafny.ULong other){
        this(other.value());
    }

    public UInt(dafny.UByte other){
        this(other.value());
    }

    public static int compare(UInt x, UInt y){
        return Integer.compareUnsigned(x.inner, y.inner);
    }

    public int compareTo(UInt other){
        return Integer.compareUnsigned(inner, other.inner);
    }

    public int value(){
        return inner;
    }

    public int intValue(){
        return inner;
    }

    public long longValue(){
        return Integer.toUnsignedLong(inner);
    }

    public BigInteger asBigInteger() {
        return BigInteger.valueOf(Integer.toUnsignedLong(inner));
    }

    //Invariant that other.inner is positive, so no underflow check needed
    //todo: determine what to do if there is overflow ever
    //addExact will throw an error if there is overflow
    public UInt add(UInt other){
        assert Integer.toUnsignedLong(inner) + Integer.toUnsignedLong(other.inner) <= 0xffffffffl : "Precondition Failure";
        return new UInt(inner+other.inner);
    }

    //Invariant that other.inner is positive, so no overflow check needed
    public UInt subtract(UInt other){
        assert Integer.compareUnsigned(inner, other.inner) >= 0: "Precondition Failure";
        return new UInt(inner-other.inner);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public UInt multiply(UInt other){
        assert Integer.toUnsignedLong(inner) * Integer.toUnsignedLong(other.inner) <= 0xffffffffl : "Precondition Failure";
        return new UInt(inner*other.inner);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public UInt divide(UInt other){
        assert other.inner != 0 : "Precondition Failure";
        return new UInt(Integer.divideUnsigned(inner, other.inner));
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public UInt mod(UInt other){
        assert other.inner != 0 : "Precondition Failure";
        return new UInt(Integer.remainderUnsigned(inner, other.inner));
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        UInt o = (UInt) obj;
        return inner == o.inner;
    }

    @Override
    public int hashCode() {
        return Integer.hashCode(inner);
    }

    @Override
    public String toString() {
        return Integer.toUnsignedString(inner);
    }

    public UInt xor(UInt other){
        return new UInt(inner ^ other.inner);
    }

    public UInt or(UInt other){
        return new UInt(inner | other.inner);
    }

    public UInt and(UInt other){
        return new UInt(inner & other.inner);
    }

    public UInt not(){
        return new UInt(~inner);
    }

    public UInt shiftLeft(int i){
        return new UInt(inner << i);
    }

    public UInt shiftRight(int i){
        return new UInt(inner >>> i);
    }
}
