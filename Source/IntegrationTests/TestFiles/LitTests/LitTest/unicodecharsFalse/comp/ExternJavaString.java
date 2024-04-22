package dafny;

public class ExternJavaString {
    public static String getStringFromFile() {
        // Let's pretend the following is read from a file:
        return "this is some possible / text that / may have come from a file";
    }
}
