package DafnyClasses;

import java.math.BigInteger;

// Dafny bytes are default unsigned, whereas they are signed in Java, and there is no unsigned equivalent
public class DafnyByte{
    private int inner;
    public final static int MAXVALUE = 0xff;

    public DafnyByte(){
        inner = 0;
    }

    public DafnyByte(byte by){
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedInt(by);
    }

    public DafnyByte(int i){
        assert 0 <= i && i <= MAXVALUE : "Precondition Failure";
        inner = i;
    }

    public DafnyByte(DafnyByte other) {
        inner = other.inner;
    }

    public DafnyByte(BigInteger i){
        assert i.compareTo(BigInteger.ZERO) >= 0 && i.compareTo(BigInteger.valueOf(MAXVALUE)) <= 0 : "Precondition Failure";
        inner = i.intValue();
    }

    public static int compare(DafnyByte x, DafnyByte y){
        return Integer.compareUnsigned(x.inner, y.inner);
    }

    public int compareTo(DafnyByte other){
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

    public byte byteValue() { return (byte) inner; }

    //Invariant that other.inner is positive, so no underflow check needed
    public DafnyByte add(DafnyByte other){
        int i = inner + other.inner;
        assert i <= MAXVALUE: "Precondition Failure";
        return new DafnyByte(i);
    }

    //Invariant that other.inner is positive, so no overflow check needed
    public DafnyByte subtract(DafnyByte other){
        int i = inner - other.inner;
        assert i >= 0: "Precondition Failure";
        return new DafnyByte(i);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public DafnyByte multiply(DafnyByte other){
        int i = inner * other.inner;
        assert i <= MAXVALUE: "Precondition Failure";
        return new DafnyByte(i);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public DafnyByte divide(DafnyByte other){
        assert other.inner != 0 : "Precondition Failure";
        return new DafnyByte(inner/other.inner);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public DafnyByte mod(DafnyByte other){
        assert other.inner != 0 : "Precondition Failure";
        return new DafnyByte(inner%other.inner);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != getClass()) return false;
        DafnyByte o = (DafnyByte) obj;
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

    public DafnyByte xor(DafnyByte other){
        return new DafnyByte(inner ^ other.inner);
    }

    public DafnyByte or(DafnyByte other){
        return new DafnyByte(inner | other.inner);
    }

    public DafnyByte and(DafnyByte other){
        return new DafnyByte(inner & other.inner);
    }

    public DafnyByte not(){
        return new DafnyByte(~inner);
    }

    public DafnyByte shiftLeft(int i){
        return new DafnyByte(inner << i);
    }

    public DafnyByte shiftRight(int i){
        return new DafnyByte(inner >> i);
    }
}
