using System.Collections.Specialized;
using Microsoft.Boogie;

namespace NS;

public class Example {
  private enum Q { ORDINAL, Other }

  private class Gen<T> {
  }

  private class Cons<T> : Gen<T> {
    private T hd;
    private Q type;
    private Gen<T> tl;

    public Cons(T t, Q q, Gen<T> tl) {
      this.hd = t;
      this.type = q;
      this.tl = tl;
    }
  }

  private class Empty<T> : Gen<T> {
  }

  public Example() {
    var g = new Cons<string>("A", Q.Other, new Cons<string>("B", Q.ORDINAL, new Empty<string>()));
    Console.WriteLine(g);
  }
}