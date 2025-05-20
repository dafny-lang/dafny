package Std.Concurrent;

import dafny.*;

public class AtomicBox<T> {

    private volatile T val;

    public AtomicBox(T t) {
    }

    public AtomicBox(dafny.TypeDescriptor td) {
    }
    public void __ctor(T t) {
        val = t;
    }

    public void Put(T t) {
        val = t;
    }

    public T Get() {
        return val;
    }

}