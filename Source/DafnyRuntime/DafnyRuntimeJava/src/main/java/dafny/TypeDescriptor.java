// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

package dafny;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;
import java.util.function.Function;

public abstract class TypeDescriptor<T> {
    final Class<T> boxedClass;
    final Class<?> unboxedClass;

    TypeDescriptor(Class<T> javaClass) {
        this(javaClass, javaClass);
    }

    TypeDescriptor(Class<T> boxedClass, Class<?> unboxedClass) {
        this.boxedClass = boxedClass;
        this.unboxedClass = unboxedClass;
    }

    public final boolean isPrimitive() {
        return unboxedClass.isPrimitive();
    }

    public abstract T defaultValue();

    public abstract boolean isInstance(Object object);

    public abstract TypeDescriptor<?> arrayType();

    public final Object newArray(int length) {
        // Unlike most others, this Array operation is fast
        return java.lang.reflect.Array.newInstance(unboxedClass, length);
    }

    public final Object newArray(int ... dims) {
        return java.lang.reflect.Array.newInstance(unboxedClass, dims);
    }

    public abstract T getArrayElement(Object array, int index);

    public abstract void setArrayElement(Object array, int index, T value);

    public final int getArrayLength(Object array) {
        // Unlike most others, this Array operation is fast
        return java.lang.reflect.Array.getLength(array);
    }

    public abstract Object cloneArray(Object array);

    public abstract void fillArray(Object array, T value);

    public final Object fillThenReturnArray(Object array, T value) {
        fillArray(array, value);
        return array;
    }

    @SuppressWarnings("all")
    public final void copyArrayTo(Object src, int srcPos,
            Object dest, int destPos, int length) {
        System.arraycopy(src, srcPos, dest, destPos, length);
    }

    public abstract boolean arrayDeepEquals(Object array1, Object array2);

    // TODO: Benchmark this to see if it's slow (better to copy and paste for
    // each class so that setArrayElement is inlined?)
    public Object toArray(Collection<T> coll) {
        Object arr = newArray(coll.size());
        int i = 0;
        for (T elt : coll) {
            setArrayElement(arr, i++, elt);
        }
        return arr;
    }

    @Override
    public String toString() {
        return boxedClass.toString();
    }

    public static <T> TypeDescriptor<T> reference(Class<T> javaClass) {
        return referenceWithDefault(javaClass, null);
    }

    public static <T> TypeDescriptor<T> referenceWithDefault(
            Class<T> javaClass, T defaultValue) {
        return referenceWithInitializer(javaClass, () -> defaultValue);
    }

    public static <T> TypeDescriptor<T> referenceWithInitializer(
            Class<T> javaClass, Initializer<T> initializer) {
        return new ReferenceType<T>(javaClass, initializer);
    }

    public static TypeDescriptor<Byte> byteWithDefault(byte d) {
        return new ByteType(d);
    }

    public static TypeDescriptor<Short> shortWithDefault(short d) {
        return new ShortType(d);
    }

    public static TypeDescriptor<Integer> intWithDefault(int d) {
        return new IntType(d);
    }

    public static TypeDescriptor<Long> longWithDefault(long d) {
        return new LongType(d);
    }

    public static TypeDescriptor<Boolean> booleanWithDefault(boolean d) {
        return new BooleanType(d);
    }

    public static TypeDescriptor<Character> charWithDefault(char d) {
        return new CharType(d);
    }

    public static TypeDescriptor<CodePoint> unicodeCharWithDefault(char d) {
        return new UnicodeCharType(CodePoint.valueOf(d));
    }

    @FunctionalInterface
    public interface Initializer<T> {
        T defaultValue();
    }

    public static final TypeDescriptor<Byte> BYTE = new ByteType((byte)0);
    public static final TypeDescriptor<Short> SHORT = new ShortType((short)0);
    public static final TypeDescriptor<Integer> INT = new IntType(0);
    public static final TypeDescriptor<Long> LONG = new LongType(0L);
    public static final TypeDescriptor<Boolean> BOOLEAN = new BooleanType(Boolean.FALSE);
    public static final TypeDescriptor<Character> CHAR = new CharType('D');  // See CharType.DefaultValue in Dafny source code
    public static final TypeDescriptor<CodePoint> UNICODE_CHAR = new UnicodeCharType(CodePoint.valueOf((int)'D'));

    public static final TypeDescriptor<BigInteger> BIG_INTEGER =
            referenceWithDefault(BigInteger.class, BigInteger.ZERO);
    public static final TypeDescriptor<BigRational> BIG_RATIONAL =
            referenceWithDefault(BigRational.class, BigRational.ZERO);

    public static final TypeDescriptor<Object> OBJECT = reference(Object.class);

    public static final TypeDescriptor<byte[]> BYTE_ARRAY = reference(byte[].class);
    public static final TypeDescriptor<short[]> SHORT_ARRAY = reference(short[].class);
    public static final TypeDescriptor<int[]> INT_ARRAY = reference(int[].class);
    public static final TypeDescriptor<long[]> LONG_ARRAY = reference(long[].class);
    public static final TypeDescriptor<boolean[]> BOOLEAN_ARRAY = reference(boolean[].class);
    public static final TypeDescriptor<char[]> CHAR_ARRAY = reference(char[].class);
    public static final TypeDescriptor<int[]> UNICODE_CHAR_ARRAY = reference(int[].class);

    public static <A, R> TypeDescriptor<Function<A, R>> function(TypeDescriptor<A> argType, TypeDescriptor<R> returnType) {
        @SuppressWarnings("unchecked")
        Class<Function<A, R>> functionClass =
                (Class<Function<A, R>>) (Class<?>) Function.class;
        // XXX This seems to allow non-nullable types to have null values (since
        // arrow types are allowed as "(0)"-constrained type arguments), but
        // it's consistent with other backends.
        return reference(functionClass);
    }

    // TODO: Cache this somehow?
    public static <T> TypeDescriptor<T> findType(Class<?> cls, TypeDescriptor<?> ... args) {
        Class<?>[] typeMethodArgTypes = new Class<?>[args.length];
        for (int i = 0; i < args.length; i++) {
            typeMethodArgTypes[i] = TypeDescriptor.class;
        }
        try {
            Method typeMethod = cls.getMethod("_typeDescriptor", typeMethodArgTypes);
            @SuppressWarnings("unchecked")
            TypeDescriptor<T> ans = (TypeDescriptor<T>) typeMethod.invoke(null, (Object[]) args);
            return ans;
        } catch (NoSuchMethodException | IllegalAccessException e) {
            @SuppressWarnings("unchecked")
            TypeDescriptor<T> ans = (TypeDescriptor<T>) reference(cls);
            return ans;
        } catch (InvocationTargetException e) {
            Throwable cause = e.getCause();
            if (cause instanceof RuntimeException) {
                throw (RuntimeException) cause;
            } else if (cause instanceof Error) {
                throw (Error) cause;
            } else {
                throw new RuntimeException(cause);
            }
        }
    }

    private static final class ReferenceType<T> extends TypeDescriptor<T> {
        private final Initializer<T> initializer;
        private TypeDescriptor<?> arrayType;

        public ReferenceType(Class<T> javaClass, Initializer<T> initializer) {
            super(javaClass);

            assert !javaClass.isPrimitive();

            this.initializer = initializer;
        }

        @Override
        public T defaultValue() {
            return initializer.defaultValue();
        }

        @Override
        public boolean isInstance(Object object) {
            return boxedClass.isInstance(object);
        }

        @Override
        public TypeDescriptor<?> arrayType() {
            if (arrayType == null) {
                arrayType = reference(newArray(0).getClass());
            }
            return arrayType;
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
        public Object cloneArray(Object array) {
            @SuppressWarnings("unchecked")
            T[] castArray = (T[]) array;
            return castArray.clone();
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

        @Override
        public boolean arrayDeepEquals(Object array1, Object array2) {
            @SuppressWarnings("unchecked")
            T[] castArray1 = (T[]) array1;
            @SuppressWarnings("unchecked")
            T[] castArray2 = (T[]) array2;
            return Arrays.deepEquals(castArray1, castArray2);
        }
    }

    private static final class ByteType extends TypeDescriptor<Byte> {
        private final Byte DEFAULT;

        public ByteType(byte d) {
            super(Byte.TYPE);
            DEFAULT = d;
        }

        @Override
        public Byte defaultValue() {
            return DEFAULT;
        }

        @Override
        public boolean isInstance(Object object) {
            return object instanceof Byte;
        }

        @Override
        public TypeDescriptor<?> arrayType() {
            return BYTE_ARRAY;
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
        public Object cloneArray(Object array) {
            return ((byte[]) array).clone();
        }

        @Override
        public void fillArray(Object array, Byte value) {
            Arrays.fill((byte[]) array, value);
        }

        @Override
        public boolean arrayDeepEquals(Object array1, Object array2) {
            byte[] castArray1 = (byte[]) array1, castArray2 = (byte[]) array2;
            return Arrays.equals(castArray1, castArray2);
        }
    }

    private static final class ShortType extends TypeDescriptor<Short> {
        private final Short DEFAULT;

        public ShortType(short d) {
            super(Short.TYPE);
            DEFAULT = d;
        }

        @Override
        public Short defaultValue() {
            return DEFAULT;
        }

        @Override
        public boolean isInstance(Object object) {
            return object instanceof Short;
        }

        @Override
        public TypeDescriptor<?> arrayType() {
            return SHORT_ARRAY;
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
        public Object cloneArray(Object array) {
            return ((short[]) array).clone();
        }

        @Override
        public void fillArray(Object array, Short value) {
            Arrays.fill((short[]) array, value);
        }

        @Override
        public boolean arrayDeepEquals(Object array1, Object array2) {
            short[] castArray1 = (short[]) array1, castArray2 = (short[]) array2;
            return Arrays.equals(castArray1, castArray2);
        }
    }

    private static final class IntType extends TypeDescriptor<Integer> {
        private final Integer DEFAULT;

        public IntType(int d) {
            super(Integer.TYPE);
            DEFAULT = d;
        }

        @Override
        public Integer defaultValue() {
            return DEFAULT;
        }

        @Override
        public boolean isInstance(Object object) {
            return object instanceof Integer;
        }

        @Override
        public TypeDescriptor<?> arrayType() {
            return INT_ARRAY;
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
        public Object cloneArray(Object array) {
            return ((int[]) array).clone();
        }

        @Override
        public void fillArray(Object array, Integer value) {
            Arrays.fill((int[]) array, value);
        }

        @Override
        public boolean arrayDeepEquals(Object array1, Object array2) {
            int[] castArray1 = (int[]) array1, castArray2 = (int[]) array2;
            return Arrays.equals(castArray1, castArray2);
        }
    }

    private static final class LongType extends TypeDescriptor<Long> {
        private final Long DEFAULT;

        public LongType(long d) {
            super(Long.TYPE);
            DEFAULT = d;
        }

        @Override
        public Long defaultValue() {
            return DEFAULT;
        }

        @Override
        public boolean isInstance(Object object) {
            return object instanceof Long;
        }

        @Override
        public TypeDescriptor<?> arrayType() {
            return LONG_ARRAY;
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
        public Object cloneArray(Object array) {
            return ((long[]) array).clone();
        }

        @Override
        public void fillArray(Object array, Long value) {
            Arrays.fill((long[]) array, value);
        }

        @Override
        public boolean arrayDeepEquals(Object array1, Object array2) {
            long[] castArray1 = (long[]) array1, castArray2 = (long[]) array2;
            return Arrays.equals(castArray1, castArray2);
        }
    }

    private static final class BooleanType extends TypeDescriptor<Boolean> {
        private final Boolean DEFAULT;

        public BooleanType(boolean d) {
            super(Boolean.TYPE);
            DEFAULT = d;
        }

        @Override
        public Boolean defaultValue() {
            return DEFAULT;
        }

        @Override
        public boolean isInstance(Object object) {
            return object instanceof Boolean;
        }

        @Override
        public TypeDescriptor<?> arrayType() {
            return BOOLEAN_ARRAY;
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
        public Object cloneArray(Object array) {
            return ((boolean[]) array).clone();
        }

        @Override
        public void fillArray(Object array, Boolean value) {
            Arrays.fill((boolean[]) array, value);
        }

        @Override
        public boolean arrayDeepEquals(Object array1, Object array2) {
            boolean[] castArray1 = (boolean[]) array1, castArray2 = (boolean[]) array2;
            return Arrays.equals(castArray1, castArray2);
        }
    }

    private static final class CharType extends TypeDescriptor<Character> {
        private final Character DEFAULT;

        public CharType(char d) {
            super(Character.TYPE);
            DEFAULT = d;
        }

        @Override
        public Character defaultValue() {
            return DEFAULT;
        }

        @Override
        public boolean isInstance(Object object) {
            return object instanceof Character;
        }

        @Override
        public TypeDescriptor<?> arrayType() {
            return CHAR_ARRAY;
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
        public Object cloneArray(Object array) {
            return ((char[]) array).clone();
        }

        @Override
        public void fillArray(Object array, Character value) {
            Arrays.fill((char[]) array, value);
        }

        @Override
        public boolean arrayDeepEquals(Object array1, Object array2) {
            char[] castArray1 = (char[]) array1, castArray2 = (char[]) array2;
            return Arrays.equals(castArray1, castArray2);
        }
    }

    private static final class UnicodeCharType extends TypeDescriptor<CodePoint> {
        private final CodePoint DEFAULT;

        public UnicodeCharType(CodePoint d) {
            super(CodePoint.class, Integer.TYPE);
            DEFAULT = d;
        }

        @Override
        public CodePoint defaultValue() {
            return DEFAULT;
        }

        @Override
        public boolean isInstance(Object object) {
            return object instanceof CodePoint;
        }

        @Override
        public TypeDescriptor<?> arrayType() {
            return UNICODE_CHAR_ARRAY;
        }

        @Override
        public CodePoint getArrayElement(Object array, int index) {
            return CodePoint.valueOf(((int[]) array)[index]);
        }

        @Override
        public void setArrayElement(Object array, int index, CodePoint value) {
            ((int[]) array)[index] = value.value();
        }

        @Override
        public Object cloneArray(Object array) {
            return ((int[]) array).clone();
        }

        @Override
        public void fillArray(Object array, CodePoint value) {
            Arrays.fill((int[]) array, value.value());
        }

        @Override
        public boolean arrayDeepEquals(Object array1, Object array2) {
            int[] castArray1 = (int[]) array1, castArray2 = (int[]) array2;
            return Arrays.equals(castArray1, castArray2);
        }
    }
}
