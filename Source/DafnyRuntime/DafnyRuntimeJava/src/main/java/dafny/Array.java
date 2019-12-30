package dafny;

import java.util.Arrays;

/**
 * A wrapper for an array that may be of primitive type.  Essentially acts as
 * one "big box" for many primitives, as an alternative to putting each in their
 * own box.  Much faster than using {@link java.lang.reflect.Array} operations
 * to operate on possibly-primitive arrays.
 * <p>
 * This class only offers a minimal set of operations for the purpose of
 * compiling Dafny code to Java.  For things like copying ranges of elements,
 * use {@link #unwrap()} to get at the underlying object and then use, for
 * instance, {@link System#arraycopy} (which, unlike
 * {@link java.lang.reflect.Array#get} and {@link java.lang.reflect.Array#set},
 * is fast).
 *
 * @param <T> The type of the elements in the array, or if that type is
 *            primitive, the boxed version of that type (e.g., {@link Integer}
 *            for int).
 */
public abstract class Array<T> {
    // Hacky way to support getting this length the same way as a real array
    public final int length;

    Array(int length) {
        this.length = length;
    }

    public abstract T get(int index);

    public abstract void set(int index, T value);

    public abstract void fill(T value);

    public abstract Object unwrap();

    @SuppressWarnings("unchecked")
    public static <T> Array<T> wrap(Object array) {
        // TODO: Figure out if there's a faster way to do this than a linear
        // search, or if there's a better order to check things in (this is just
        // an uneducated guess at putting common cases first).
        if (array == null) {
            return null;
        } else if (array instanceof Object[]) {
            // Arrays shouldn't be covariant, but they are, so this case covers
            // all reference types
            return new ObjectArray<T>((T[]) array);
        } else if (array instanceof byte[]) {
            return (Array<T>) new ByteArray((byte[]) array);
        } else if (array instanceof char[]) {
            return (Array<T>) new CharArray((char[]) array);
        } else if (array instanceof int[]) {
            return (Array<T>) new IntArray((int[]) array);
        } else if (array instanceof double[]) {
            return (Array<T>) new DoubleArray((double[]) array);
        } else if (array instanceof boolean[]) {
            return (Array<T>) new BooleanArray((boolean[]) array);
        } else if (array instanceof long[]) {
            return (Array<T>) new LongArray((long[]) array);
        } else if (array instanceof float[]) {
            return (Array<T>) new FloatArray((float[]) array);
        } else if (array instanceof short[]) {
            return (Array<T>) new ShortArray((short[]) array);
        } else {
            throw new IllegalArgumentException(
                    "Expected array, got argument of type: " + array.getClass());
        }
    }

    public static <T> Array<T> wrap(T[] array) {
        assert array == null || !array.getClass().getComponentType().isPrimitive();

        return array == null ? null : new ObjectArray<T>(array);
    }

    public static Array<Byte> wrap(byte[] array) {
        return array == null ? null : new ByteArray(array);
    }

    public static Array<Short> wrap(short[] array) {
        return array == null ? null : new ShortArray(array);
    }

    public static Array<Integer> wrap(int[] array) {
        return array == null ? null : new IntArray(array);
    }

    public static Array<Long> wrap(long[] array) {
        return array == null ? null : new LongArray(array);
    }

    public static Array<Boolean> wrap(boolean[] array) {
        return array == null ? null : new BooleanArray(array);
    }

    public static Array<Character> wrap(char[] array) {
        return array == null ? null : new CharArray(array);
    }

    public static Array<Float> wrap(float[] array) {
        return array == null ? null : new FloatArray(array);
    }

    public static Array<Double> wrap(double[] array) {
        return array == null ? null : new DoubleArray(array);
    }

    /**
     * Allocate a multidimensional array whose innermost layer is wrapped in
     * {@link Array} objects.  There must be at least two dimensions given.
     *
     * @return An object of type <tt>Array&lt;T>[]...[]</tt>, where there is one
     * pair of brackets for each dimension besides the innermost.
     */
    public static <T> Object[] newInstances(
            Type<T> elmtType, int ... dims) {
        return newInstances(elmtType, null, dims);
    }

    /**
     * Allocate a multidimensional array whose innermost layer is wrapped in
     * {@link Array} objects, initializing all elements with the given value.
     * There must be at least two dimensions.
     *
     * @return An object of type <tt>Array&lt;T>[]...[]</tt>, where there is one
     * pair of brackets for each dimension besides the innermost.
     */
    public static <T> Object[] newInstances(
            Type<T> elmtType, T value, int ... dims) {
        assert dims.length >= 2;

        int[] outerDims = Arrays.copyOfRange(dims, 0, dims.length - 1);
        Object[] arrays = (Object[])
                java.lang.reflect.Array.newInstance(Array.class, outerDims);

        init(arrays, elmtType, value, 0, dims);

        return arrays;
    }

    private static <T> void init(
            Object[] arrays, Type<T> elmtType, T value, int d, int ... dims) {
        if (d == dims.length - 2) {
            for (int i = 0; i < dims[d]; i++) {
                Array<T> inner = elmtType.newArray(dims[d]);
                if (value != null) {
                    inner.fill(value);
                }
                arrays[i] = inner;
            }
        } else {
            for (int i = 0; i < dims[d]; i++) {
                init((Object[]) arrays[i], elmtType, value, d+1, dims);
            }
        }
    }

    public static Object unwrap(Array<?> array) {
        return array == null ? null : array.unwrap();
    }

    public static <T> T[] unwrapObjects(Array<T> array) {
        return array == null ? null : ((ObjectArray<T>) array).array;
    }

    public static byte[] unwrapBytes(Array<Byte> array) {
        return array == null ? null : ((ByteArray) array).array;
    }

    public static short[] unwrapShorts(Array<Short> array) {
        return array == null ? null : ((ShortArray) array).array;
    }

    public static int[] unwrapInts(Array<Integer> array) {
        return array == null ? null : ((IntArray) array).array;
    }

    public static long[] unwrapLongs(Array<Long> array) {
        return array == null ? null : ((LongArray) array).array;
    }

    public static boolean[] unwrapBooleans(Array<Boolean> array) {
        return array == null ? null : ((BooleanArray) array).array;
    }

    public static char[] unwrapChars(Array<Character> array) {
        return array == null ? null : ((CharArray) array).array;
    }

    public static float[] unwrapFloats(Array<Float> array) {
        return array == null ? null : ((FloatArray) array).array;
    }

    public static double[] unwrapDoubles(Array<Double> array) {
        return array == null ? null : ((DoubleArray) array).array;
    }

    @Override
    public final String toString() {
        // Arrays don't have a useful toString method, but this is supposed to
        // be an exact proxy for a real Java array, so we defer to them anyway
        return unwrap().toString();
    }

    @SuppressWarnings("unchecked")
    private static final Type<Array<?>> TYPE =
            (Type<Array<?>>) (Type<?>) Type.reference(Array.class);
    @SuppressWarnings("unchecked")
    public static <T> Type<Array<T>> _type() {
        return (Type<Array<T>>) (Type<?>) TYPE;
    }
}

final class ObjectArray<T> extends Array<T> {
    final T[] array;

    ObjectArray(T[] array) {
        super(array.length);
        this.array = array;
    }

    @Override
    public T get(int index) {
        return array[index];
    }

    @Override
    public void set(int index, T value) {
        array[index] = value;
    }

    @Override
    public void fill(T value) {
        int n = array.length;
        for (int i = 0; i < n; i++) {
            array[i] = value;
        }
    }

    @Override
    public Object unwrap() {
        return array;
    }
}

final class ByteArray extends Array<Byte> {
    final byte[] array;

    ByteArray(byte[] array) {
        super(array.length);
        this.array = array;
    }

    @Override
    public Byte get(int index) {
        return array[index];
    }

    @Override
    public void set(int index, Byte value) {
        array[index] = value;
    }

    @Override
    public void fill(Byte value) {
        byte nativeValue = value;
        int n = array.length;
        for (int i = 0; i < n; i++) {
            array[i] = nativeValue;
        }
    }

    @Override
    public Object unwrap() {
        return array;
    }
}

final class ShortArray extends Array<Short> {
    final short[] array;

    ShortArray(short[] array) {
        super(array.length);
        this.array = array;
    }

    @Override
    public Short get(int index) {
        return array[index];
    }

    @Override
    public void set(int index, Short value) {
        array[index] = value;
    }

    @Override
    public void fill(Short value) {
        short nativeValue = value;
        int n = array.length;
        for (int i = 0; i < n; i++) {
            array[i] = nativeValue;
        }
    }

    @Override
    public Object unwrap() {
        return array;
    }
}

final class IntArray extends Array<Integer> {
    final int[] array;

    IntArray(int[] array) {
        super(array.length);
        this.array = array;
    }

    @Override
    public Integer get(int index) {
        return array[index];
    }

    @Override
    public void set(int index, Integer value) {
        array[index] = value;
    }

    @Override
    public void fill(Integer value) {
        int nativeValue = value;
        int n = array.length;
        for (int i = 0; i < n; i++) {
            array[i] = nativeValue;
        }
    }

    @Override
    public Object unwrap() {
        return array;
    }
}

final class LongArray extends Array<Long> {
    final long[] array;

    LongArray(long[] array) {
        super(array.length);
        this.array = array;
    }

    @Override
    public Long get(int index) {
        return array[index];
    }

    @Override
    public void set(int index, Long value) {
        array[index] = value;
    }

    @Override
    public void fill(Long value) {
        long nativeValue = value;
        int n = array.length;
        for (int i = 0; i < n; i++) {
            array[i] = nativeValue;
        }
    }

    @Override
    public Object unwrap() {
        return array;
    }
}

final class BooleanArray extends Array<Boolean> {
    final boolean[] array;

    BooleanArray(boolean[] array) {
        super(array.length);
        this.array = array;
    }

    @Override
    public Boolean get(int index) {
        return array[index];
    }

    @Override
    public void set(int index, Boolean value) {
        array[index] = value;
    }

    @Override
    public void fill(Boolean value) {
        boolean nativeValue = value;
        int n = array.length;
        for (int i = 0; i < n; i++) {
            array[i] = nativeValue;
        }
    }

    @Override
    public Object unwrap() {
        return array;
    }
}

final class CharArray extends Array<Character> {
    final char[] array;

    CharArray(char[] array) {
        super(array.length);
        this.array = array;
    }

    @Override
    public Character get(int index) {
        return array[index];
    }

    @Override
    public void set(int index, Character value) {
        array[index] = value;
    }

    @Override
    public void fill(Character value) {
        char nativeValue = value;
        int n = array.length;
        for (int i = 0; i < n; i++) {
            array[i] = nativeValue;
        }
    }

    @Override
    public Object unwrap() {
        return array;
    }
}

final class FloatArray extends Array<Float> {
    final float[] array;

    FloatArray(float[] array) {
        super(array.length);
        this.array = array;
    }

    @Override
    public Float get(int index) {
        return array[index];
    }

    @Override
    public void set(int index, Float value) {
        array[index] = value;
    }

    @Override
    public void fill(Float value) {
        float nativeValue = value;
        int n = array.length;
        for (int i = 0; i < n; i++) {
            array[i] = nativeValue;
        }
    }

    @Override
    public Object unwrap() {
        return array;
    }
}

final class DoubleArray extends Array<Double> {
    final double[] array;

    DoubleArray(double[] array) {
        super(array.length);
        this.array = array;
    }

    @Override
    public Double get(int index) {
        return array[index];
    }

    @Override
    public void set(int index, Double value) {
        array[index] = value;
    }

    @Override
    public void fill(Double value) {
        double nativeValue = value;
        int n = array.length;
        for (int i = 0; i < n; i++) {
            array[i] = nativeValue;
        }
    }

    @Override
    public Object unwrap() {
        return array;
    }
}