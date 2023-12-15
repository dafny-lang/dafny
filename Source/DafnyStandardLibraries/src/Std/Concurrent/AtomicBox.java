package Std.Concurrent;

import dafny.*;

public class AtomicBox<T> {

    private volatile T val;

    public AtomicBox(T t) {
        val = t;
    }

    public AtomicBox(dafny.TypeDescriptor td, T t) {
        this(t);
    }

    public void Put(T t) {
        val = t;
    }

    public T Get() {
        return val;
    }

}