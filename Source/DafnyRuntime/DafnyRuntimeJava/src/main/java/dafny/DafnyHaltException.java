package dafny;

public class DafnyHaltException extends RuntimeException {

    public DafnyHaltException(String message) {
        super(message);
    }
}