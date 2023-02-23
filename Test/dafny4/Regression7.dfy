// RUN: %dafny /rprint:"%t.rprint" /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ListLibrary {
  datatype List<B> = Nil | Cons(head: B, tail: List<B>)
}

module Q {
  import LL = ListLibrary

  datatype Queue<T> = FQ(front: LL.List<T>, rear: LL.List<T>)

  function MyCons<W>(w: W, ws: LL.List<W>): LL.List<W>
  {
    LL.Cons(w, ws)
  }

  method Test<A>(q: Queue<A>, x: A) returns (r: LL.List<A>)
  {
    var r0 := MyCons(x, q.rear);
    var r1 := var qr := q.rear; LL.Cons(x, qr);
    var r2 := LL.Cons(x, q.rear);  // this once said "type Queue<T> does not have a member rear"
    assert r0.tail == r1.tail == r2.tail;
    r := r2;
  }
}

method Main()
{
  var q := Q.FQ(ListLibrary.Nil, ListLibrary.Nil);
  var x := 28.0;
  var ll := Q.Test(q, x);
  print ll, "\n";
}
