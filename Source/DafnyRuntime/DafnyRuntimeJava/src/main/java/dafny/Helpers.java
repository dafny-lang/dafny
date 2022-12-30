// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

package dafny;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Array;
import java.math.BigInteger;
import java.math.BigDecimal;
import java.util.Collection;
import java.util.Iterator;
import java.util.function.*;
import java.util.ArrayList;
import java.lang.Iterable;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class Helpers {

    public static DafnySequence<? extends DafnySequence<? extends Character>> FromMainArguments(String[] args) {
       @SuppressWarnings("unchecked")
       TypeDescriptor<DafnySequence<? extends Character>> type = DafnySequence.<Character>_typeDescriptor(TypeDescriptor.CHAR);
       dafny.Array<DafnySequence<? extends Character>> dafnyArgs = dafny.Array.newArray(type, args.length + 1);
       dafnyArgs.set(0, DafnySequence.asString("java"));
       for (int i = 0; i < args.length; i++) dafnyArgs.set(i + 1, DafnySequence.asString(args[i]));
       return DafnySequence.fromArray(type, dafnyArgs);
    }
    
    public static DafnySequence<? extends DafnySequence<? extends CodePoint>> UnicodeFromMainArguments(String[] args) {
       @SuppressWarnings("unchecked")
       TypeDescriptor<DafnySequence<? extends CodePoint>> type = DafnySequence.<CodePoint>_typeDescriptor(TypeDescriptor.UNICODE_CHAR);
       dafny.Array<DafnySequence<? extends CodePoint>> dafnyArgs = dafny.Array.newArray(type, args.length + 1);
       dafnyArgs.set(0, DafnySequence.asUnicodeString("java"));
       for (int i = 0; i < args.length; i++) dafnyArgs.set(i + 1, DafnySequence.asUnicodeString(args[i]));
       return DafnySequence.fromArray(type, dafnyArgs);
    }

    public static String ToStringLiteral(DafnySequence<? extends CodePoint> dafnyString) {
        StringBuilder builder = new StringBuilder();
        builder.append("\"");
        for (CodePoint codePoint : dafnyString) {
            AppendCodePointWithEscaping(builder, codePoint.value());
        }
        builder.append("\"");
        return builder.toString();
    }

    // Note this is a Dafny character literal, not necessarily a valid Java character literal
    public static String ToCharLiteral(int codePoint) {
        StringBuilder builder = new StringBuilder();
        builder.append("\'");
        AppendCodePointWithEscaping(builder, codePoint);
        builder.append("\'");
        return builder.toString();
    }

    private static void AppendCodePointWithEscaping(StringBuilder builder, int codePoint) {
        switch (codePoint) {
            case '\n':
                builder.append("\\n");
                break;
            case '\r':
                builder.append("\\r");
                break;
            case '\t':
                builder.append("\\t");
                break;
            case '\0':
                builder.append("\\0");
                break;
            case '\'':
                builder.append("\\'");
                break;
            case '\"':
                builder.append("\\\"");
                break;
            case '\\':
                builder.append("\\\\");
                break;
            default:    
                builder.appendCodePoint(codePoint);
                break;
        }
        
    }
    
    public static <T> boolean Quantifier(Iterable<T> vals, boolean frall, Predicate<T> pred) {
        for (T t : vals) {
            if (pred.test(t) != frall) {
                return !frall;
            }
        }
        return frall;
    }

    public static <T> T Id(T t) {
        return t;
    }

    public static <T, U> U Let(T t, Function<T, U> f) {
        return f.apply(t);
    }

    /* Returns Iterable in range [lo, hi-1] if lo and hi are both not null.
    If lo == null, returns Iterable that infinitely ranges down from hi-1.
    If hi == null, returns Iterable that infinitely ranges up from lo.
     */
    public static Iterable<BigInteger> IntegerRange(BigInteger lo, BigInteger hi) {
        assert lo != null || hi != null;
        if(lo == null) {
            return () -> {
                Stream<BigInteger> infiniteStream = Stream.iterate(hi.subtract(BigInteger.ONE), i -> i.subtract(BigInteger.ONE));
                return infiniteStream.iterator();
            };
        } else if(hi == null) {
            return () -> {
                Stream<BigInteger> infiniteStream = Stream.iterate(lo, i -> i.add(BigInteger.ONE));
                return infiniteStream.iterator();
            };
        } else {
            return () -> new Iterator<BigInteger>() {
                private BigInteger i = lo;

                @Override
                public boolean hasNext() {
                    return i.compareTo(hi) < 0;
                }

                @Override
                public BigInteger next() {
                    BigInteger j = i;
                    i = i.add(BigInteger.ONE);
                    return j;
                }
            };
        }
    }

    public static Iterable<BigInteger> AllIntegers() {
        return () -> new Iterator<BigInteger>() {
            BigInteger i = BigInteger.ZERO;

            @Override
            public boolean hasNext() {
                return true;
            }

            @Override
            public BigInteger next() {
                BigInteger j = i;
                if (i.equals(BigInteger.ZERO))
                    i = BigInteger.ONE;
                else if (i.signum() > 0)
                    i = i.negate();
                else
                    i = i.negate().add(BigInteger.ONE);
                return j;
            }
        };
    }

    public static Iterable<Boolean> AllBooleans() {
        return () -> IntStream.range(0, 2).<Boolean>mapToObj(i -> i == 1).iterator();
    }

    public static Iterable<Character> AllChars() {
        return () -> IntStream.range(0, 0x1_0000).<Character>mapToObj(i -> Character.valueOf((char)i)).iterator();
    }

    // Note we don't use CodePoint here because this is only used in the implementation of quantification,
    // where we want to enumerate primitive values, and it's challenging to customize that logic
    // to unbox CodePoints manually.
    public static Iterable<Integer> AllUnicodeChars() {
        return () -> IntStream.concat(IntStream.range(0, 0xD800), 
                                      IntStream.range(0xE000, 0x11_0000)).iterator();
    }

    public static <G> String toString(G g) {
        if (g == null) {
            return "null";
        } else {
            return g.toString();
        }
    }

    public static int toInt(BigInteger i) {
        return i.intValue();
    }

    public static void outOfRange(String msg) {
        throw new dafny.DafnyHaltException(msg);
    }

    public static int toIntChecked(BigInteger i, String msg) {
        int r = i.intValue();
        if (!BigInteger.valueOf(r).equals(i)) {
          msg = (msg != null ? msg : "value out of range for a 32-bit int") + ": " + i;
          outOfRange(msg);
        }
        return r;
    }

    public static int toIntChecked(long i, String msg) {
        int r = (int)i;
        if (r != i) {
          msg = (msg != null ? msg : "value out of range for a 32-bit int") + ": " + i;
          outOfRange(msg);
        }
        return r;
    }

    public static int unsignedToIntChecked(byte i) {
        int r = unsignedToInt(i);
        return r;
    }

    public static int unsignedToIntChecked(short i) {
        int r = unsignedToInt(i);
        return r;
    }

    public static int unsignedToIntChecked(long i, String msg) {
        int r = unsignedToInt(i);
        if (r != i) {
          msg = (msg != null ? msg : "value out of range for a 32-bit int") + ": " + i;
          outOfRange(msg);
        }
        return r;
    }

    public static int toInt(int i) {
        return i;
    }

    public static int toInt(long l) {
        return (int) l;
    }

    public static int unsignedToInt(byte x) {
        return ((int)x) & 0xFF;
    }

    public static int unsignedToInt(short x) {
        return ((int)x) & 0xFFFF;
    }

    public static int unsignedToInt(long x) {
        return (int)x;
    }

    private final static BigInteger ULONG_LIMIT = new BigInteger("18446744073709551616");  // 0x1_0000_0000_0000_0000

    public static BigInteger unsignedLongToBigInteger(long l) {
        if (0 <= l) {
            return BigInteger.valueOf(l);
        } else {
            return BigInteger.valueOf(l).add(ULONG_LIMIT);
        }
    }

    public static byte divideUnsignedByte(byte a, byte b) {
        return (byte)Integer.divideUnsigned(((int)a) & 0xFF, ((int)b) & 0xFF);
    }

    public static short divideUnsignedShort(short a, short b) {
        return (short)Integer.divideUnsigned(((int)a) & 0xFFFF, ((int)b) & 0xFFFF);
    }

    public static byte remainderUnsignedByte(byte a, byte b) {
        return (byte)Integer.remainderUnsigned(((int)a) & 0xFF, ((int)b) & 0xFF);
    }

    public static short remainderUnsignedShort(short a, short b) {
        return (short)Integer.remainderUnsigned(((int)a) & 0xFFFF, ((int)b) & 0xFFFF);
    }

    public static void withHaltHandling(Runnable runnable) {
        try {
            runnable.run();
        } catch (DafnyHaltException e) {
            System.out.println("[Program halted] " + e.getMessage());
            System.exit(1);
        }
    }
}


