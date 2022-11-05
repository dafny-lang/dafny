package dafny;

/**
 * An int wrapper type just like java.lang.Integer,
 * but used as a more type-safe reference to a Unicode scalar value
 * specifially, which corresponds to the Dafny `char` type
 * when using --unicode-char.
 */
public final class CodePoint {

    public static CodePoint valueOf(int value) {
        // TODO: cache common values just like the other boxing classes?
        return new CodePoint(value);
    }

    private final int value;
    
    private CodePoint(int value) {
        // if (!Character.isValidCodePoint(value) || Character.isSurrogate((char)value)) {
        //     throw new IllegalArgumentException("Code point out of range: " + value);
        // }
        this.value = value;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null || !(obj instanceof CodePoint)) {
            return false;
        }

        return value == ((CodePoint)obj).value;
    }

    @Override
    public int hashCode() {
        return Integer.hashCode(value);
    }

    public int value() {
        return value;
    }

    @Override
    public String toString() {
        return Helpers.ToCharLiteral(value);
    }
}