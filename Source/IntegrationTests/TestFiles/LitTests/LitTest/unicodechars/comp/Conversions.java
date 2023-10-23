package Util;

public class Conversions {
    public static String ToJavaString(dafny.DafnySequence<? extends dafny.CodePoint> s) {
        return s.verbatimString();
    }
}
