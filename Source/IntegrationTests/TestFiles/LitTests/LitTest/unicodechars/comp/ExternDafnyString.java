package dafny;

public class ExternDafnyString {
    public static dafny.DafnySequence<? extends CodePoint> getStringFromFile() {
        // Let's pretend the following is read from a file:
        String js = "this is some possible / text that / may have come from a file";
        // Convert this Java string to a Dafny string before returning:
        return dafny.DafnySequence.asUnicodeString(js);
    }
}
