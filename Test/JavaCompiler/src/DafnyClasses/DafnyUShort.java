package DafnyClasses;

public class DafnyUShort {
    private int inner;
    public final static int MAXVALUE = 0xffff;
    public DafnyUShort(byte by){
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedInt(by);
    }

    public DafnyUShort(short sh){
        //simply casting to an int will preserve the sign
        inner = Short.toUnsignedInt(sh);
    }

    public DafnyUShort(int i){
        assert 0 <= i && i <= MAXVALUE : "Precondition Failure";
        inner = i;
    }

    public DafnyUShort(DafnyUShort other){
        inner = other.inner;
    }

    public static int compare(DafnyUShort x, DafnyUShort y){
        return Integer.compareUnsigned(x.inner,y.inner);
    }

    public int compareTo(DafnyUShort other){
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
    public DafnyUShort add(DafnyUShort other){
        int i = inner + other.inner;
        assert i <= MAXVALUE: "Precondition Failure";
        return new DafnyUShort(i);
    }

    //Invariant that other.inner is positive, so no overflow check needed
    public DafnyUShort subtract(DafnyUShort other){
        int i = inner - other.inner;
        assert i >= 0: "Precondition Failure";
        return new DafnyUShort(i);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public DafnyUShort multiply(DafnyUShort other){
        int i = inner * other.inner;
        assert i <= MAXVALUE: "Precondition Failure";
        return new DafnyUShort(i);
    }
    
    //Invariant that other.inner is positive, so only nonzero check needed
    public DafnyUShort divide(DafnyUShort other){
        assert other.inner != 0 : "Precondition Failure";
        return new DafnyUShort(inner/other.inner);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public DafnyUShort mod(DafnyUShort other) {
        assert other.inner != 0 : "Precondition Failure";
        return new DafnyUShort(inner % other.inner);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        DafnyUShort o = (DafnyUShort) obj;
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

    public DafnyUShort xor(DafnyUShort other){
        return new DafnyUShort(inner ^ other.inner);
    }

    public DafnyUShort or(DafnyUShort other){
        return new DafnyUShort(inner | other.inner);
    }

    public DafnyUShort and(DafnyUShort other){
        return new DafnyUShort(inner & other.inner);
    }

    public DafnyUShort not(){
        return new DafnyUShort(~inner);
    }

    public DafnyUShort shiftLeft(int i){
        return new DafnyUShort(inner << i);
    }

    public DafnyUShort shiftRight(int i){
        return new DafnyUShort(inner >> i);
    }
}
