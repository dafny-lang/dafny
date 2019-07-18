package DafnyClasses;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Array;
import java.math.BigInteger;
import java.math.BigDecimal;
import java.util.Collection;
import java.util.function.*;

public class Helpers {

    public static <T> boolean Quantifier(Collection<T> vals, boolean frall, Predicate<T> pred) {
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
            if (!s.startsWith("class "))
                return Class.forName(s).newInstance();
            if (s.startsWith("class [")) {
                String xs = s.substring(8);
                xs = xs.replace(";", "");
                return Array.newInstance(Class.forName(xs), 0);
            }
            switch (s) {
                case "class java.math.BigInteger":
                    return BigInteger.ZERO;
                case "class java.lang.Boolean":
                    return new Boolean(false);
                case "class java.math.BigDecimal":
                    return new BigDecimal(0);
                default:
                    String xs = s.substring(6);
                    return Class.forName(xs).newInstance();
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    public static ArrayList<BigInteger> IntegerRange(BigInteger lo, BigInteger hi) {
        ArrayList<BigInteger> arr = new ArrayList<>();
        while (lo.compareTo(hi) < 0) {
            arr.add(lo);
            lo = lo.add(new BigInteger("1"));
        }
        return arr;
    }
}
}

