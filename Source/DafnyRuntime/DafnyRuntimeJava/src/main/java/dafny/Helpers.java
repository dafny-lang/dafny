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
    
    public static Object getDefault(String s) {
        if (s == null || s.startsWith("interface "))
            return null;
        try {
            if (!s.startsWith("class ")){
                Object o = Class.forName(s).newInstance();
                if(o.toString().contains("@"))
                    return null;
                else
                    return o;
            }
            if (s.startsWith("class [")) {
                return null;
            }
            switch (s) {
                case "class java.math.BigInteger":
                    return BigInteger.ZERO;
                case "class java.lang.Boolean":
                    return new Boolean(false);
                case "class java.math.BigDecimal":
                    return new BigDecimal(0);
                case "class java.lang.Character":
                    return 'D';
                case "class dafny.DafnySequence":
                    return DafnySequence.<Object> empty();
                default:
                    String xs = s.substring(6);
                    Object o = Class.forName(xs).newInstance();
                    if(o.toString().contains("@"))
                        return null;
                    else
                        return o;
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    /* Returns Iterable in range [lo, hi-1] if lo and hi are both not null.
    If lo == null, returns Iterable that infinitely ranges down from hi-1.
    If hi == null, returns Iterable that infinitely ranges up from lo.
     */
    public static Iterable<BigInteger> IntegerRange(BigInteger lo, BigInteger hi) {
        assert lo != null || hi != null;
        if(lo == null) {
            hi = hi.subtract(BigInteger.ONE);
            Stream<BigInteger> infiniteSteam = Stream.iterate(hi, i -> i.subtract(BigInteger.ONE));
            return (Iterable<BigInteger>) infiniteSteam::iterator;
        } else if(hi == null) {
            Stream<BigInteger> infiniteSteam = Stream.iterate(lo, i -> i.add(BigInteger.ONE));
            return (Iterable<BigInteger>) infiniteSteam::iterator;
        } else {
            ArrayList<BigInteger> arr = new ArrayList<>();
            while (lo.compareTo(hi) < 0) {
                arr.add(lo);
                lo = lo.add(BigInteger.ONE);
            }
            return arr;
        }
    }

    public static Iterable<BigInteger> AllIntegers() {
        return new AllIntegers();
    }

    public static Character createCharacter(UByte t) {
        assert 0 <= t.intValue() && t.intValue() <= 65535;
        return new Character((char)t.intValue());
    }

    public static Character createCharacter(UInt t) {
        assert 0 <= t.value() && t.value() <= 65535;
        return new Character((char)t.value());
    }

    public static Character createCharacter(ULong t) {
        assert 0 <= t.value() && t.value() <= 65535;
        return new Character((char)t.value());
    }

    public static Character createCharacter(long t) {
        assert 0 <= t && t <= 65535;
        return new Character((char)t);
    }

    public static Class getClassUnsafe(String s) {
        try {
            return Class.forName(s);
        }
        catch(ClassNotFoundException e) {
            throw new RuntimeException("Class " + s + " not found.");
        }
    }

    public static <G> String toString(G g) {
        if (g == null) {
            return "null";
        } else {
            return g.toString();
        }
    }
}


