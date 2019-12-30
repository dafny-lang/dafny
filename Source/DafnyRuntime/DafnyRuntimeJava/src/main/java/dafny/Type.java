package dafny;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.function.Function;

public abstract class Type<T> {
    private final Class<T> javaClass;

    Type(Class<T> javaClass) {
        this.javaClass = javaClass;
    }

    public abstract T defaultValue();

    public abstract Array<T> newArray(int length);

    public abstract T getArrayElement(Object array, int index);

    public abstract void setArrayElement(Object array, int index, T value);

    public abstract void fillArray(Object array, T value);

    public final Class<T> getJavaClass() {
        return javaClass;
    }

    public final Array<T> newArray(int length, T value) {
        Array<T> array = newArray(length);
        array.fill(value);
        return array;
    }

    public final Object newUnwrappedArray(int length) {
        return java.lang.reflect.Array.newInstance(getJavaClass(), length);
    }

    public final Object newUnwrappedArray(int length, T value) {
        Object array = newUnwrappedArray(length);
        fillArray(array, value);
        return array;
    }

    @Override
    public String toString() {
        return getJavaClass().toString();
    }

    public static <T> Type<T> reference(Class<T> javaClass) {
        return referenceWithDefault(javaClass, null);
    }

    public static <T> Type<T> referenceWithDefault(
            Class<T> javaClass, T defaultValue) {
        return referenceWithInitializer(javaClass, () -> defaultValue);
    }

    public static <T> Type<T> referenceWithInitializer(
            Class<T> javaClass, Initializer<T> initializer) {
        return new ReferenceType<T>(javaClass, initializer);
    }

    @FunctionalInterface
    public interface Initializer<T> {
        T defaultValue();
    }

    public static final Type<Byte> BYTE = new ByteType();
    public static final Type<Short> SHORT = new ShortType();
    public static final Type<Integer> INT = new IntType();
    public static final Type<Long> LONG = new LongType();
    public static final Type<Boolean> BOOLEAN = new BooleanType();
    public static final Type<Character> CHAR = new CharType();
    public static final Type<Float> FLOAT = new FloatType();
    public static final Type<Double> DOUBLE = new DoubleType();

    public static final Type<BigInteger> BIG_INTEGER =
            referenceWithDefault(BigInteger.class, BigInteger.ZERO);
    public static final Type<BigRational> BIG_RATIONAL =
            referenceWithDefault(BigRational.class, BigRational.ZERO);

    public static final Type<Object> OBJECT = reference(Object.class);

    public static final Type<byte[]> BYTE_ARRAY = reference(byte[].class);
    public static final Type<short[]> SHORT_ARRAY = reference(short[].class);
    public static final Type<int[]> INT_ARRAY = reference(int[].class);
    public static final Type<long[]> LONG_ARRAY = reference(long[].class);
    public static final Type<boolean[]> BOOLEAN_ARRAY = reference(boolean[].class);
    public static final Type<char[]> CHAR_ARRAY = reference(char[].class);
    public static final Type<float[]> FLOAT_ARRAY = reference(float[].class);
    public static final Type<double[]> DOUBLE_ARRAY = reference(double[].class);

    public static <T> Type<T[]> unwrappedArrayOfReference(Type<T> eltType) {
        assert !eltType.javaClass.isPrimitive();

        @SuppressWarnings("unchecked")
        Class<T[]> arrayClass = (Class<T[]>) eltType.newUnwrappedArray(0).getClass();
        return reference(arrayClass);
    }

    public static <A, R> Type<Function<A, R>> function(Type<A> argType, Type<R> returnType) {
        @SuppressWarnings("unchecked")
        Class<Function<A, R>> functionClass =
                (Class<Function<A, R>>) (Class<?>) Function.class;
        // XXX This seems to allow non-nullable types to have null values (since
        // arrow types are allowed as "(0)"-constrained type arguments), but
        // it's consistent with other backends.
        return reference(functionClass);
    }

    private static final class ReferenceType<T> extends Type<T> {
        private final Initializer<T> initializer;

        public ReferenceType(Class<T> javaClass, Initializer<T> initializer) {
            super(javaClass);

            assert !javaClass.isPrimitive();

            this.initializer = initializer;
        }

        @Override
        public T defaultValue() {
            return initializer.defaultValue();
        }

        public Array<T> newArray(int length) {
            @SuppressWarnings("unchecked")
            // This cast only works because we know that T is *not* a (boxed)
            // primitive type
            T[] array = (T[])
                    java.lang.reflect.Array.newInstance(getJavaClass(), length);
            return Array.wrap(array);
        }

        @Override
        public T getArrayElement(Object array, int index) {
            @SuppressWarnings("unchecked")
            T[] castArray = (T[]) array;
            return castArray[index];
        }

        @Override
        public void setArrayElement(Object array, int index, T value) {
            @SuppressWarnings("unchecked")
            T[] castArray = (T[]) array;
            castArray[index] = value;
        }

        @Override
        public void fillArray(Object array, T value) {
            @SuppressWarnings("unchecked")
            T[] castArray = (T[]) array;
            int n = castArray.length;
            for (int i = 0; i < n; i++) {
                castArray[i] = value;
            }
        }
    }

    private static final class ByteType extends Type<Byte> {
        private static final Byte DEFAULT = 0;

        public ByteType() {
            super(Byte.TYPE);
        }

        @Override
        public Byte defaultValue() {
            return DEFAULT;
        }

        @Override
        public Array<Byte> newArray(int length) {
            return Array.wrap(new byte[length]);
        }

        @Override
        public Byte getArrayElement(Object array, int index) {
            return ((byte[]) array)[index];
        }

        @Override
        public void setArrayElement(Object array, int index, Byte value) {
            ((byte[]) array)[index] = value;
        }

        @Override
        public void fillArray(Object array, Byte value) {
            Arrays.fill((byte[]) array, value);
        }
    }

    private static final class ShortType extends Type<Short> {
        private static final Short DEFAULT = 0;

        public ShortType() {
            super(Short.TYPE);
        }

        @Override
        public Short defaultValue() {
            return DEFAULT;
        }

        @Override
        public Array<Short> newArray(int length) {
            return Array.wrap(new short[length]);
        }

        @Override
        public Short getArrayElement(Object array, int index) {
            return ((short[]) array)[index];
        }

        @Override
        public void setArrayElement(Object array, int index, Short value) {
            ((short[]) array)[index] = value;
        }

        @Override
        public void fillArray(Object array, Short value) {
            Arrays.fill((short[]) array, value);
        }
    }

    private static final class IntType extends Type<Integer> {
        private static final Integer DEFAULT = 0;

        public IntType() {
            super(Integer.TYPE);
        }

        @Override
        public Integer defaultValue() {
            return DEFAULT;
        }

        @Override
        public Array<Integer> newArray(int length) {
            return Array.wrap(new int[length]);
        }

        @Override
        public Integer getArrayElement(Object array, int index) {
            return ((int[]) array)[index];
        }

        @Override
        public void setArrayElement(Object array, int index, Integer value) {
            ((int[]) array)[index] = value;
        }

        @Override
        public void fillArray(Object array, Integer value) {
            Arrays.fill((int[]) array, value);
        }
    }

    private static final class LongType extends Type<Long> {
        private static final Long DEFAULT = 0L;

        public LongType() {
            super(Long.TYPE);
        }

        @Override
        public Long defaultValue() {
            return DEFAULT;
        }

        @Override
        public Array<Long> newArray(int length) {
            return Array.wrap(new long[length]);
        }

        @Override
        public Long getArrayElement(Object array, int index) {
            return ((long[]) array)[index];
        }

        @Override
        public void setArrayElement(Object array, int index, Long value) {
            ((long[]) array)[index] = value;
        }

        @Override
        public void fillArray(Object array, Long value) {
            Arrays.fill((long[]) array, value);
        }
    }

    private static final class BooleanType extends Type<Boolean> {
        public BooleanType() {
            super(Boolean.TYPE);
        }

        @Override
        public Boolean defaultValue() {
            return Boolean.FALSE;
        }

        @Override
        public Array<Boolean> newArray(int length) {
            return Array.wrap(new boolean[length]);
        }

        @Override
        public Boolean getArrayElement(Object array, int index) {
            return ((boolean[]) array)[index];
        }

        @Override
        public void setArrayElement(Object array, int index, Boolean value) {
            ((boolean[]) array)[index] = value;
        }

        @Override
        public void fillArray(Object array, Boolean value) {
            Arrays.fill((boolean[]) array, value);
        }
    }

    private static final class CharType extends Type<Character> {
        private static final Character DEFAULT = 'D';

        public CharType() {
            super(Character.TYPE);
        }

        @Override
        public Character defaultValue() {
            return DEFAULT;
        }

        @Override
        public Array<Character> newArray(int length) {
            return Array.wrap(new char[length]);
        }

        @Override
        public Character getArrayElement(Object array, int index) {
            return ((char[]) array)[index];
        }

        @Override
        public void setArrayElement(Object array, int index, Character value) {
            ((char[]) array)[index] = value;
        }

        @Override
        public void fillArray(Object array, Character value) {
            Arrays.fill((char[]) array, value);
        }
    }

    private static final class FloatType extends Type<Float> {
        private static final Float DEFAULT = 0.0f;

        public FloatType() {
            super(Float.TYPE);
        }

        @Override
        public Float defaultValue() {
            return DEFAULT;
        }

        @Override
        public Array<Float> newArray(int length) {
            return Array.wrap(new float[length]);
        }

        @Override
        public Float getArrayElement(Object array, int index) {
            return ((float[]) array)[index];
        }

        @Override
        public void setArrayElement(Object array, int index, Float value) {
            ((float[]) array)[index] = value;
        }

        @Override
        public void fillArray(Object array, Float value) {
            Arrays.fill((float[]) array, value);
        }
    }

    private static final class DoubleType extends Type<Double> {
        private static final Double DEFAULT = 0.0;

        public DoubleType() {
            super(Double.TYPE);
        }

        @Override
        public Double defaultValue() {
            return DEFAULT;
        }

        @Override
        public Array<Double> newArray(int length) {
            return Array.wrap(new double[length]);
        }

        @Override
        public Double getArrayElement(Object array, int index) {
            return ((double[]) array)[index];
        }

        @Override
        public void setArrayElement(Object array, int index, Double value) {
            ((double[]) array)[index] = value;
        }

        @Override
        public void fillArray(Object array, Double value) {
            Arrays.fill((double[]) array, value);
        }
    }
}
