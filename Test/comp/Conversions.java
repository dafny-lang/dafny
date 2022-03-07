package Util;

public class Conversions {
    public static String ToJavaString(dafny.DafnySequence<? extends Character> s) {
        return s.verbatimString();
    }
}
