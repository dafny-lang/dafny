package Library;

// The Java compiler doesn't support Dafny methods in extern libraries
public class Mixed {
    public static void P() {
        System.out.println("Mixed.P");
    }
    public static void M() {
        System.out.println("Mixed.M");
    }
}