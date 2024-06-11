package Std.Concurrent;

import java.util.concurrent.locks.ReentrantLock;

public class Lock {

    private final ReentrantLock lock = new ReentrantLock();

    public void __ctor() {}

    public void __Lock() {
        lock.lock();
    }

    public void Unlock() {
        lock.unlock();
    }
}