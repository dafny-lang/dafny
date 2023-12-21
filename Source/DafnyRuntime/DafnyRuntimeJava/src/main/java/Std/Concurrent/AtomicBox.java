package Std.Concurrent;

import dafny.*;

public class AtomicBox<T> {

    private volatile T val;

    public void __ctor(T t) {
        val = t;
    }
    
    public AtomicBox() {
    }

    public AtomicBox(dafny.TypeDescriptor td) {
        this();
    }

    public void Put(T t) {
        val = t;
    }

    public T Get() {
        return val;
    }

}