package dafny;

import java.lang.reflect.Array;
import java.math.BigInteger;
import java.util.function.Function;

public abstract class Type<T> {
    // Only allow this package to implement
    Type() { }

    public abstract T defaultValue();

    abstract Class<T> javaClass();

    public static <T> Type<T> referenceType(Class<T> javaClass) {
        return referenceTypeWithDefault(javaClass, null);
    }

    public static <T> Type<T> referenceTypeWithDefault(
            Class<T> javaClass, T defaultValue) {
        return referenceTypeWithInitializer(javaClass, () -> defaultValue);
    }

    public static <T> Type<T> referenceTypeWithInitializer(
            Class<T> javaClass, Initializer<T> initializer) {
        return new ReferenceType<T>(javaClass, initializer);
    }

    @FunctionalInterface
    public interface Initializer<T> {
        T defaultValue();
    }

    public static final Type<Byte> BYTE =
            referenceTypeWithDefault(Byte.class, (byte) 0);
    public static final Type<Short> SHORT =
            referenceTypeWithDefault(Short.class, (short) 0);
    public static final Type<Integer> INT =
            referenceTypeWithDefault(Integer.class, 0);
    public static final Type<Long> LONG =
            referenceTypeWithDefault(Long.class, 0L);
    public static final Type<Boolean> BOOLEAN =
            referenceTypeWithDefault(Boolean.class, Boolean.FALSE);
    public static final Type<Character> CHAR =
            referenceTypeWithDefault(Character.class, 'D');
    public static final Type<Float> FLOAT =
            referenceTypeWithDefault(Float.class, 0.0f);
    public static final Type<Double> DOUBLE =
            referenceTypeWithDefault(Double.class, 0.0);

    public static final Type<BigInteger> BIG_INTEGER =
            referenceTypeWithDefault(BigInteger.class, BigInteger.ZERO);
    public static final Type<BigRational> BIG_RATIONAL =
            referenceTypeWithDefault(BigRational.class, BigRational.ZERO);

    public static final Type<Object> OBJECT =
            referenceType(Object.class);

    public static <T> Type<T[]> array(Type<T> elementType) {
        // This is okay only because elementType.javaClass() is never primitive.
        @SuppressWarnings("unchecked")
        Class<T[]> arrayClass = (Class<T[]>)
                Array.newInstance(elementType.javaClass(), 0).getClass();
        return referenceType(arrayClass);
    }

    public static <A, R> Type<Function<A, R>> function(Type<A> argType, Type<R> returnType) {
        @SuppressWarnings("unchecked")
        Class<Function<A, R>> functionClass =
                (Class<Function<A, R>>) (Class<?>) Function.class;
        // XXX This seems to allow non-nullable types to have null values (since
        // arrow types are allowed as "(0)"-constrained type arguments), but
        // it's consistent with other backends.
        return referenceType(functionClass);
    }

    private static final class ReferenceType<T> extends Type<T> {
        private final Class<T> javaClass;
        private final Initializer<T> initializer;

        public ReferenceType(Class<T> javaClass, Initializer<T> initializer) {
            this.javaClass = javaClass;
            this.initializer = initializer;
        }

        @Override
        public T defaultValue() {
            return initializer.defaultValue();
        }

        @Override
        Class<T> javaClass() {
            return javaClass;
        }

        @Override
        public String toString() {
            // TODO: Handle generic arguments
            return javaClass.toString();
        }
    }
}
