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

    public static Iterable<Character> AllChars() {
        return () -> IntStream.range(0, 0x1000).<Character>mapToObj(i -> Character.valueOf((char)i)).iterator();
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

    public static int toInt(int i) {
        return i;
    }

    public static int toInt(long l) {
        return (int) l;
    }

    private final static BigInteger ULONG_LIMIT = new BigInteger("18446744073709551616");  // 0x1_0000_0000_0000_0000

    public static BigInteger unsignedLongToBigInteger(long l) {
        if (0 <= l) {
            return BigInteger.valueOf(l);
        } else {
            return BigInteger.valueOf(l).add(ULONG_LIMIT);
        }
    }
    
    public static void withHaltHandling(Runnable runnable) {
        try {
            runnable.run();
        } catch (DafnyHaltException e) {
            System.err.println("Program halted: " + e.getMessage());
        }
    }
}


