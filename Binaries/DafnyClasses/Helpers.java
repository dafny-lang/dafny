package DafnyClasses;

import java.util.Collection;
import java.util.function.*;
import java.util.ArrayList;
import java.math.BigInteger;

public class Helpers {


    public static <T> boolean Quantifier(Collection<T> vals, boolean frall, Predicate<T> pred){
        for (T t : vals){
            if (pred.test(t) != frall){
                return !frall;
            }
        }

        return frall;
    }

    public static <T> T Id(T t){
        return t;
    }

    public static <T, U> U Let(T t, Function<T, U> f){
        return f.apply(t);
    }

    public static ArrayList<BigInteger> IntegerRange(BigInteger lo, BigInteger hi) {
        ArrayList<BigInteger> arr = new ArrayList<>();
        while(lo.compareTo(hi) < 0) {
            arr.add(lo);
            lo = lo.add(new BigInteger("1"));
        }
        return arr;
    }
}

