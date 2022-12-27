// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

package dafny;

import java.util.List;

/**
 * A wrapper for an array that may be of primitive type.  Essentially acts as
 * one "big box" for many primitives, as an alternative to putting each in their
 * own box.  Much faster than using {@link java.lang.reflect.Array} operations
 * to operate on possibly-primitive arrays.
 *
 * This isn't used by generated Dafny code, which directly uses values of type
 * Object when the element type isn't known, relying on a {@link Type} passed
 * in.  It's much more pleasant to use, and more type-safe, than the bare
 * {@link Type} operations, however, so extern implementors may be interested.
 * It is also used to implement {@link DafnySequence}.
 *
 * @param <T> The type of the elements in the array, or if that type is
 *            primitive, the boxed version of that type (e.g., {@link Integer}
 *            for int).
 */
public final class Array<T> implements Cloneable {
    private final TypeDescriptor<T> eltType;
    private final Object array;

    private Array(TypeDescriptor<T> eltType, Object array) {
        this.eltType = eltType;
        this.array = array;
    }

    public static <T> Array<T> newArray(TypeDescriptor<T> eltType, int length) {
        return new Array<T>(eltType, eltType.newArray(length));
    }

    public static <T> Array<T> fromList(TypeDescriptor<T> eltType, List<T> elements) {
        return new Array<T>(eltType, eltType.toArray(elements));
    }

    public TypeDescriptor<T> elementType() {
        return eltType;
    }

    public Object unwrap() {
        return array;
    }

    public T get(int index) {
        return eltType.getArrayElement(array, index);
    }

    public void set(int index, T value) {
        eltType.setArrayElement(array, index, value);
    }

    public int length() {
        return eltType.getArrayLength(array);
    }

    public void fill(T value) {
        eltType.fillArray(array, value);
    }

    public Array<T> copy() {
        return new Array<T>(eltType, eltType.cloneArray(array));
    }

    @SuppressWarnings("SuspiciousSystemArraycopy")
    public void copy(int offset, Array<T> to, int toOffset, int length) {
        System.arraycopy(this.array, offset, to.array, toOffset, length);
    }

    public Array<T> copyOfRange(int lo, int hi) {
        Array<T> newArray = newArray(eltType, hi - lo);
        copy(lo, newArray, 0, hi - lo);
        return newArray;
    }

    public boolean deepEquals(Array<T> other) {
        return eltType.arrayDeepEquals(this.array, other.array);
    }

    public static <T> Array<T> wrap(TypeDescriptor<T> eltType, Object array) {
        assert eltType.arrayType().isInstance(array);

        return new Array<T>(eltType, array);
    }

    // Note: We need the element type passed in here because otherwise the
    // actual type of the array might not be T[] but S[] where S is a subclass
    // of T.
    public static <T> Array<T> wrap(TypeDescriptor<T> eltType, T[] array) {
        return new Array<T>(eltType, array);
    }

    public static Array<Byte> wrap(byte[] array) {
        return new Array<Byte>(TypeDescriptor.BYTE, array);
    }

    public static Array<Short> wrap(short[] array) {
        return new Array<Short>(TypeDescriptor.SHORT, array);
    }

    public static Array<Integer> wrap(int[] array) {
        return new Array<Integer>(TypeDescriptor.INT, array);
    }

    public static Array<Long> wrap(long[] array) {
        return new Array<Long>(TypeDescriptor.LONG, array);
    }

    public static Array<Boolean> wrap(boolean[] array) {
        return new Array<Boolean>(TypeDescriptor.BOOLEAN, array);
    }

    public static Array<Character> wrap(char[] array) {
        return new Array<Character>(TypeDescriptor.CHAR, array);
    }

    public static Object unwrap(Array<?> array) {
        return array.unwrap();
    }

    @SuppressWarnings("unchecked")
    public static <T> T[] unwrapObjects(Array<T> array) {
        return (T[]) array.array;
    }

    public static byte[] unwrapBytes(Array<Byte> array) {
        return (byte[]) array.array;
    }

    public static short[] unwrapShorts(Array<Short> array) {
        return (short[]) array.array;
    }

    public static int[] unwrapInts(Array<Integer> array) {
        return (int[]) array.array;
    }

    public static long[] unwrapLongs(Array<Long> array) {
        return (long[]) array.array;
    }

    public static boolean[] unwrapBooleans(Array<Boolean> array) {
        return (boolean[]) array.array;
    }

    public static char[] unwrapChars(Array<Character> array) {
        return (char[]) array.array;
    }
}
