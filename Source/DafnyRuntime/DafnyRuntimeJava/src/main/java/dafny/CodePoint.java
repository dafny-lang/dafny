package dafny;

/**
 * An int wrapper type just like java.lang.Integer,
 * but used as a more type-safe reference to a Unicode scalar value
 * specifically, which corresponds to the Dafny `char` type
 * when using --unicode-char.
 */
public final class CodePoint {

    // Caching a subset of values just like the built-in box types like Character.
    private static class CodePointCache {
        private CodePointCache(){}

        static final int MAX_CACHE_KEY = 128;

        static final CodePoint cache[] = new CodePoint[MAX_CACHE_KEY];

        static {
            for (int i = 0; i < cache.length; i++) {
                cache[i] = new CodePoint(i);
            }
        }
    }

    public static CodePoint valueOf(int value) {
        if (0 <= value && value < CodePointCache.MAX_CACHE_KEY) {
            return CodePointCache.cache[value];
        }
        return new CodePoint(value);
    }

    private final int value;
    
    private CodePoint(int value) {
        if (!Character.isValidCodePoint(value) || (Character.MIN_SURROGATE <= value && value <= Character.MAX_SURROGATE)) {
            throw new IllegalArgumentException("Code point out of range: " + value);
        }
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