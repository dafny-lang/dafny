package DafnyClasses;

// Dafny bytes are default unsigned, whereas they are signed in Java, and there is no unsigned equivalent
public class DafnyUInt {
    private int inner;
    public final static int MAXVALUE = 0xffffffff;
    public DafnyUInt(byte by){
        //simply casting to an int will preserve the sign
        inner = Byte.toUnsignedInt(by);
    }

    public DafnyUInt(short sh){
        //simply casting to an int will preserve the sign
        inner = Short.toUnsignedInt(sh);
    }

    public DafnyUInt(int i){
        inner = i;
    }

    public DafnyUInt(long l){
        assert l <= 0xffffffffl: "Precondition Failure";
        inner = (int) l;
    }

    public DafnyUInt(){
        inner = 0;
    }

    public DafnyUInt(DafnyUInt other){
        inner = other.inner;
    }

    public static int compare(DafnyUInt x, DafnyUInt y){
        return Integer.compareUnsigned(x.inner, y.inner);
    }

    public int compareTo(DafnyUInt other){
        return Integer.compareUnsigned(inner, other.inner);
    }

    public int value(){
        return inner;
    }

    public double doubleValue(){
        return (double) Integer.toUnsignedLong(inner);
    }

    public float floatValue(){
        return (float) Integer.toUnsignedLong(inner);
    }

    public long longValue(){
        return Integer.toUnsignedLong(inner);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    //todo: determine what to do if there is overflow ever
    //addExact will throw an error if there is overflow
    public DafnyUInt add(DafnyUInt other){
        assert Integer.toUnsignedLong(inner) + Integer.toUnsignedLong(other.inner) <= 0xffffffffl : "Precondition Failure";
        return new DafnyUInt(inner+other.inner);
    }

    //Invariant that other.inner is positive, so no overflow check needed
    public DafnyUInt subtract(DafnyUInt other){
        assert Integer.compareUnsigned(inner, other.inner) >= 0: "Precondition Failure";
        return new DafnyUInt(inner-other.inner);
    }

    //Invariant that other.inner is positive, so no underflow check needed
    public DafnyUInt multiply(DafnyUInt other){
        assert Integer.toUnsignedLong(inner) * Integer.toUnsignedLong(other.inner) <= 0xffffffffl : "Precondition Failure";
        return new DafnyUInt(inner*other.inner);
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public DafnyUInt divide(DafnyUInt other){
        assert other.inner != 0 : "Precondition Failure";
        return new DafnyUInt(Integer.divideUnsigned(inner, other.inner));
    }

    //Invariant that other.inner is positive, so only nonzero check needed
    public DafnyUInt mod(DafnyUInt other){
        assert other.inner != 0 : "Precondition Failure";
        return new DafnyUInt(Integer.remainderUnsigned(inner, other.inner));
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        DafnyUInt o = (DafnyUInt) obj;
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

    public DafnyUInt xor(DafnyUInt other){
        return new DafnyUInt(inner ^ other.inner);
    }

    public DafnyUInt or(DafnyUInt other){
        return new DafnyUInt(inner | other.inner);
    }

    public DafnyUInt and(DafnyUInt other){
        return new DafnyUInt(inner & other.inner);
    }

    public DafnyUInt not(){
        return new DafnyUInt(~inner);
    }

    public DafnyUInt shiftLeft(int i){
        return new DafnyUInt(inner << i);
    }

    public DafnyUInt shiftRight(int i){
        return new DafnyUInt(inner >> i);
    }
}
