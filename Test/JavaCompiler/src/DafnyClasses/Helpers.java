package DafnyClasses;

import java.lang.reflect.InvocationTargetException;
import java.math.BigDecimal;
import java.math.BigInteger;
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

    public static Object getDefault(String s) throws ClassNotFoundException, InstantiationException, IllegalAccessException {
        if(!s.startsWith("class "))
            return Class.forName(s).newInstance();
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
    }
}

