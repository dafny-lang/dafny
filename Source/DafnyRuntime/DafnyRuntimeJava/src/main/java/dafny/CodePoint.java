package dafny;

public class CodePoint {

    private final int value;
    
    public CodePoint(int value) {
        this.value = value;
    }

    public int value() {
        return value;
    }

    @Override
    public String toString() {
        return Helpers.ToCharLiteral(value);
    }
}