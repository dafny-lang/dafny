using System;

namespace Microsoft.Dafny;

public class Lazy<T> {
  private readonly Func<T> get;
  private bool set;
  private T value;

  public Lazy(T value) {
    this.value = value;
    set = true;
  }

  public Lazy(Func<T> get) {
    this.get = get;
  }

  public T Value {
    get {
      lock (this) {
        if (!set) {
          value = get();
          set = true;
        }

        return value;
      }
    }
  }
}