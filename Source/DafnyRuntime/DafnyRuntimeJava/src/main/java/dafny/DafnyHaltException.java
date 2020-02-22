package dafny;

public class DafnyHaltException extends RuntimeException {

    public DafnyHaltException(DafnySequence<Character> message) {
        super(message.verbatimString());
    }
}