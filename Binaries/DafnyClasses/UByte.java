package dafny;

import java.math.BigInteger;

// Dafny bytes are default unsigned, whereas they are signed in Java, and there is no unsigned equivalent
public class UByte {
    private int inner;
    public final static int MAXVALUE = 0xff;
    public UByte(byte by){
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedInt(by);
    }

    public UByte(int i){
        assert 0 <= i && i <= MAXVALUE : "Precondition Failure";
        inner = i;
    }

    public UByte(UByte other){
        inner = other.inner;
    }

    public UByte(BigInteger i){
        assert i.compareTo(BigInteger.ZERO) >= 0 && i.compareTo(BigInteger.valueOf(MAXVALUE)) <= 0 : "Precondition Failure";
        inner = i.intValue();
    }

    public static int compare(UByte x, UByte y){
        return Integer.compareUnsigned(x.inner, y.inner);
    }

    public int compareTo(UByte other){
        return Integer.compareUnsigned(inner, other.inner);
    }


    public double doubleValue(){
        return (double) inner;
    }

    public float floatValue(){
        return (float) inner;
    }

    public int intValue(){
        return inner;
    }

    public long longValue(){
        return (long) inner;
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public UByte add(UByte other){
        int i = inner + other.inner;
        assert i <= MAXVALUE: "Precondition Failure";
        return new UByte(i);
    }

    //Invariant that other.inner is positive, so no overflow check needed
    public UByte subtract(UByte other){
        int i = inner - other.inner;
        assert i >= 0: "Precondition Failure";
        return new UByte(i);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public UByte multiply(UByte other){
        int i = inner * other.inner;
        assert i <= MAXVALUE: "Precondition Failure";
        return new UByte(i);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public UByte divide(UByte other){
        assert other.inner != 0 : "Precondition Failure";
        return new UByte(inner/other.inner);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public UByte mod(UByte other){
        assert other.inner != 0 : "Precondition Failure";
        return new UByte(inner%other.inner);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != getClass()) return false;
        UByte o = (UByte) obj;
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

    public UByte xor(UByte other){
        return new UByte(inner ^ other.inner);
    }

    public UByte or(UByte other){
        return new UByte(inner | other.inner);
    }

    public UByte and(UByte other){
        return new UByte(inner & other.inner);
    }

    public UByte not(){
        return new UByte(~inner);
    }

    public UByte shiftLeft(int i){
        return new UByte(inner << i);
    }

    public UByte shiftRight(int i){
        return new UByte(inner >> i);
    }
}
