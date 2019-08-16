package dafny;

import java.math.BigInteger;

// Dafny bytes are default unsigned, whereas they are signed in Java, and there is no unsigned equivalent
public class UByte {
    private int inner;
    public final static int MAXVALUE = 0xff; // 255
    public UByte(byte by){
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedInt(by);
    }

    public UByte(int i){
        assert 0 <= i && i <= MAXVALUE : "Precondition Failure";
        inner = i;
    }

    public UByte(short s){
        assert 0 <= s && s <= MAXVALUE : "Precondition Failure";
        inner = s;
    }

    public UByte(long l){
        assert 0 <= l && l <= MAXVALUE : "Precondition Failure";
        inner = (int) l;
    }

    public UByte(UByte other){
        inner = other.inner;
    }

    public UByte(dafny.UInt other){
        this(other.value());
    }

    public UByte(dafny.ULong other){
        this(other.value());
    }

    public UByte(dafny.UShort other){
        this(other.value());
    }

    public UByte(BigInteger i){
        assert 0 <= i.compareTo(BigInteger.ZERO) && i.compareTo(BigInteger.valueOf(MAXVALUE)) <= 0 : "Precondition Failure";
        inner = i.intValue();
    }

    public static int compare(UByte x, UByte y){
        return Integer.compareUnsigned(x.inner, y.inner);
    }

    public int compareTo(UByte other){
        return Integer.compareUnsigned(inner, other.inner);
    }

    public int intValue(){
        return inner;
    }

    public long longValue(){
        return (long) inner;
    }

    public byte byteValue(){
        assert 0 <= inner && inner <= MAXVALUE;
        return (byte) inner;
    }

    public byte value(){
        return byteValue();
    }

    public UByte add(UByte other){
        int i = inner + other.inner;
        i %= (MAXVALUE + 1);
        return new UByte(i);
    }

    public UByte subtract(UByte other){
        int i = inner - other.inner;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        return new UByte(i);
    }

    public UByte multiply(UByte other){
        int i = inner * other.inner;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        i %= (MAXVALUE + 1);
        return new UByte(i);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public UByte divide(UByte other){
        assert other.inner != 0 : "Precondition Failure";
        int i = inner/other.inner;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        i %= (MAXVALUE + 1);
        return new UByte(i);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public UByte mod(UByte other){
        assert other.inner != 0 : "Precondition Failure";
        int i = inner % other.inner;
        return new UByte(i);
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
        int i = inner ^ other.inner;
        return new UByte(i);
    }

    public UByte or(UByte other){
        int i = inner | other.inner;
        return new UByte(i);
    }

    public UByte and(UByte other){
        int i = inner & other.inner;
        return new UByte(i);
    }

    public UByte not(){
        int i = ~inner;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        i %= (MAXVALUE + 1);
        return new UByte(i);
    }

    public UByte shiftLeft(int i){
        i = inner << i;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        i %= (MAXVALUE + 1);
        return new UByte(i);
    }

    public UByte shiftRight(int i){
        i = inner >>> i;
        return new UByte(i);
    }
}
