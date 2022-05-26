using System;
using System.Threading;

class EasyReadWriteLock {
  private readonly ReaderWriterLockSlim slim;
  private readonly ReadDisposable readDisposable;
  private readonly WriteDisposable writeDisposable;

  public EasyReadWriteLock() {
    slim = new();
    readDisposable = new ReadDisposable(slim);
    writeDisposable = new WriteDisposable(slim);
  }

  public IDisposable EnterWriteLock() {
    slim.EnterWriteLock();
    return writeDisposable;
  }

  public IDisposable EnterReadLock() {
    slim.EnterReadLock();
    return readDisposable;
  }

  class ReadDisposable : IDisposable {
    private readonly ReaderWriterLockSlim slim;

    public ReadDisposable(ReaderWriterLockSlim slim) {
      this.slim = slim;
    }

    public void Dispose() {
      slim.ExitReadLock();
    }
  }

  class WriteDisposable : IDisposable {
    private readonly ReaderWriterLockSlim slim;

    public WriteDisposable(ReaderWriterLockSlim slim) {
      this.slim = slim;
    }

    public void Dispose() {
      slim.ExitWriteLock();
    }
  }
}
