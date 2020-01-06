package dafny;

import java.util.Arrays;
import java.util.Objects;

/**
 * A wrapper for an array that may be of primitive type.  Essentially acts as
 * one "big box" for many primitives, as an alternative to putting each in their
 * own box.  Much faster than using {@link java.lang.reflect.Array} operations
 * to operate on possibly-primitive arrays.
 *
 * @param <T> The type of the elements in the array, or if that type is
 *            primitive, the boxed version of that type (e.g., {@link Integer}
 *            for int).
 */
public abstract class Array<T> implements Cloneable {
    // Hacky way to support getting this length the same way as a real array
    public final int length;

    Array(int length) {
        this.length = length;
    }

    public abstract T get(int index);

    public abstract void set(int index, T value);

    public abstract void fill(T value);

    public final Array<T> fillThenReturn(T value) {
        fill(value);
        return this;
    }

    public abstract Object unwrap();

    public abstract Array<T> clone();

    public abstract Array<T> copyOfRange(int lo, int hi);

    // This implementation is slow due to unboxing; overridden by better versions
    // where possible
    public boolean deepEquals(Array<T> other) {
        if (length != other.length) {
            return false;
        }
        for (int i = 0; i < length; i++) {
            if (!Objects.equals(this.get(i), other.get(i))) {
                return false;
            }
        }
        return true;
    }

    @SuppressWarnings("all")
    public final void copy(int offset, Array<T> to, int toOffset, int length) {
        System.arraycopy(unwrap(), offset, to.unwrap(), toOffset, length);
    }

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

    // A dodge so that we can unconditionally generate calls to Array.wrap()
    public static <T> Array<T> wrap(Array<T> array) {
        return array;
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

    public static <T> T[] fillThenReturn(T[] array, T value) {
        Arrays.fill(array, value);
        return array;
    }

    public static byte[] fillThenReturn(byte[] array, byte value) {
        Arrays.fill(array, value);
        return array;
    }

    public static short[] fillThenReturn(short[] array, short value) {
        Arrays.fill(array, value);
        return array;
    }

    public static int[] fillThenReturn(int[] array, int value) {
        Arrays.fill(array, value);
        return array;
    }

    public static long[] fillThenReturn(long[] array, long value) {
        Arrays.fill(array, value);
        return array;
    }

    public static boolean[] fillThenReturn(boolean[] array, boolean value) {
        Arrays.fill(array, value);
        return array;
    }

    public static char[] fillThenReturn(char[] array, char value) {
        Arrays.fill(array, value);
        return array;
    }

    public static float[] fillThenReturn(float[] array, float value) {
        Arrays.fill(array, value);
        return array;
    }

    public static double[] fillThenReturn(double[] array, double value) {
        Arrays.fill(array, value);
        return array;
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

    @Override
    public Array<T> clone() {
        return new ObjectArray<T>(array.clone());
    }

    @Override
    public Array<T> copyOfRange(int lo, int hi) {
        return new ObjectArray<T>(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    public boolean deepEquals(Array<T> other) {
        if (other instanceof ObjectArray<?>) {
            return Arrays.deepEquals(array, ((ObjectArray<T>) other).array);
        } else {
            return super.deepEquals(other);
        }
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

    @Override
    public ByteArray clone() {
        return new ByteArray(array.clone());
    }

    @Override
    public Array<Byte> copyOfRange(int lo, int hi) {
        return new ByteArray(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    public boolean deepEquals(Array<Byte> other) {
        if (other instanceof ByteArray) {
            return Arrays.equals(array, ((ByteArray) other).array);
        } else {
            return super.deepEquals(other);
        }
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

    @Override
    public ShortArray clone() {
        return new ShortArray(array.clone());
    }

    @Override
    public Array<Short> copyOfRange(int lo, int hi) {
        return new ShortArray(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    public boolean deepEquals(Array<Short> other) {
        if (other instanceof ShortArray) {
            return Arrays.equals(array, ((ShortArray) other).array);
        } else {
            return super.deepEquals(other);
        }
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

    @Override
    public IntArray clone() {
        return new IntArray(array.clone());
    }

    @Override
    public Array<Integer> copyOfRange(int lo, int hi) {
        return new IntArray(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    public boolean deepEquals(Array<Integer> other) {
        if (other instanceof IntArray) {
            return Arrays.equals(array, ((IntArray) other).array);
        } else {
            return super.deepEquals(other);
        }
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

    @Override
    public LongArray clone() {
        return new LongArray(array.clone());
    }

    @Override
    public Array<Long> copyOfRange(int lo, int hi) {
        return new LongArray(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    public boolean deepEquals(Array<Long> other) {
        if (other instanceof LongArray) {
            return Arrays.equals(array, ((LongArray) other).array);
        } else {
            return super.deepEquals(other);
        }
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

    @Override
    public BooleanArray clone() {
        return new BooleanArray(array.clone());
    }

    @Override
    public Array<Boolean> copyOfRange(int lo, int hi) {
        return new BooleanArray(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    public boolean deepEquals(Array<Boolean> other) {
        if (other instanceof BooleanArray) {
            return Arrays.equals(array, ((BooleanArray) other).array);
        } else {
            return super.deepEquals(other);
        }
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


    @Override
    public CharArray clone() {
        return new CharArray(array.clone());
    }

    @Override
    public Array<Character> copyOfRange(int lo, int hi) {
        return new CharArray(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    public boolean deepEquals(Array<Character> other) {
        if (other instanceof CharArray) {
            return Arrays.equals(array, ((CharArray) other).array);
        } else {
            return super.deepEquals(other);
        }
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

    @Override
    public FloatArray clone() {
        return new FloatArray(array.clone());
    }

    @Override
    public Array<Float> copyOfRange(int lo, int hi) {
        return new FloatArray(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    public boolean deepEquals(Array<Float> other) {
        if (other instanceof FloatArray) {
            return Arrays.equals(array, ((FloatArray) other).array);
        } else {
            return super.deepEquals(other);
        }
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

    @Override
    public DoubleArray clone() {
        return new DoubleArray(array.clone());
    }

    @Override
    public Array<Double> copyOfRange(int lo, int hi) {
        return new DoubleArray(Arrays.copyOfRange(array, lo, hi));
    }

    @Override
    public boolean deepEquals(Array<Double> other) {
        if (other instanceof DoubleArray) {
            return Arrays.equals(array, ((DoubleArray) other).array);
        } else {
            return super.deepEquals(other);
        }
    }
}