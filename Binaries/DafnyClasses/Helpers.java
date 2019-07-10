package DafnyClasses;

import java.util.Collection;
import java.util.function.*;

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
}

