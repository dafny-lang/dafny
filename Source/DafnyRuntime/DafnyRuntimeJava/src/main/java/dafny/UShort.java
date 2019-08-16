package dafny;

public class UShort {
    private int inner;
    public final static int MAXVALUE = 0xffff; // 65535
    public UShort(byte by){
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedInt(by);
    }

    public UShort(short sh){
        //simply casting to an int will preserve the sign
        inner = Short.toUnsignedInt(sh);
    }

    public UShort(int i){
        assert 0 <= i && i <= MAXVALUE : "Precondition Failure";
        inner = i;
    }

    public UShort(long l){
        assert 0 <= l && l <= MAXVALUE : "Precondition Failure";
        inner = (int) l;
    }

    public UShort(){
        inner = 0;
    }

    public UShort(UShort other){
        inner = other.inner;
    }

    public UShort(dafny.UInt other){
        this(other.value());
    }

    public UShort(dafny.ULong other){
        this(other.value());
    }

    public UShort(dafny.UByte other){
        this(other.value());
    }

    public static int compare(UShort x, UShort y){
        return Integer.compareUnsigned(x.inner,y.inner);
    }

    public int compareTo(UShort other){
        return Integer.compareUnsigned(inner, other.inner);
    }

    public int intValue(){
        return inner;
    }

    public long longValue(){
        return (long) inner;
    }

    public short value() {
        return (short) inner;
    }


    public UShort add(UShort other){
        int i = inner + other.inner;
        i %= (MAXVALUE + 1);
        return new UShort(i);
    }

    public UShort subtract(UShort other){
        int i = inner - other.inner;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        return new UShort(i);
    }

    public UShort multiply(UShort other){
        int i = inner * other.inner;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        i %= (MAXVALUE + 1);
        return new UShort(i);
    }
    
    //Invariant that other.inner is positive, so only nonzero check needed
    public UShort divide(UShort other){
        assert other.inner != 0 : "Precondition Failure";
        int i = inner/other.inner;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        i %= (MAXVALUE + 1);
        return new UShort(i);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public UShort mod(UShort other) {
        assert other.inner != 0 : "Precondition Failure";
        int i = inner % other.inner;
        return new UShort(i);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        UShort o = (UShort) obj;
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

    public UShort xor(UShort other){
        int i = inner ^ other.inner;
        return new UShort(i);
    }

    public UShort or(UShort other){
        int i = inner | other.inner;
        return new UShort(i);
    }

    public UShort and(UShort other){
        int i = inner & other.inner;
        return new UShort(i);
    }

    public UShort not(){
        int i = ~inner;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        i %= (MAXVALUE + 1);
        return new UShort(i);
    }

    public UShort shiftLeft(int i){
        i = inner << i;
        if(i < 0) {
            i = (MAXVALUE + 1 + i)%(MAXVALUE + 1);
        }
        i %= (MAXVALUE + 1);
        return new UShort(i);
    }

    public UShort shiftRight(int i){
        i = inner >>> i;
        return new UShort(i);
    }
}
