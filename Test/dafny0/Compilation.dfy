// The tests in this file are designed to run through the compiler.  They contain
// program snippets that are tricky to compile or whose compilation once was buggy.

module OnceBuggy {
  datatype MyDt<T> = Nil | Cons(T, MyDt<T>);

  method M<U>(x: MyDt<int>)
  {
    match (x) {
      case Cons(head, tail) =>
        var y: int := head;
      case Nil =>
    }
  }
}

// --------------------------------------------------

module CoRecursion {
  codatatype Stream<T> = More(head: T, rest: Stream);

  function method AscendingChain(n: int): Stream<int>
  {
    More(n, AscendingChain(n+1))
  }

  datatype List<T> = Nil | Cons(car: T, cdr: List);

  function method Prefix(n: nat, s: Stream): List
  {
    if n == 0 then Nil else
    Cons(s.head, Prefix(n-1, s.rest))
  }

  class Cell { var data: int; }

  // When run, the following method should print
  //   400
  //   320
  //   40
  //   41
  //   42
  method Main() {
    var m := 17;
    var cell := new Cell;
    cell.data := 40;
    var mr := More(400, More(320, AscendingChain(cell.data)));
    m := 30;
    cell.data := 60;
    var l := Prefix(5, mr);
    while (l != Nil)
      decreases l;
    {
      match (l) { case Cons(x,y) => }
      print l.car, "\n";
      l := l.cdr;
    }
  }
}

abstract module S {
  class C {
    var f: int;
    method m()
  }
}

module T refines S {
  class C {
    method m() {
      print "in T.C.m()";
    }
  }
}
module A {
   import X as S default T;
   import Y as S default T;
   import Z = T;
   static method run() {
     var x := new X.C;
     x.m();
     var y := new Y.C;
     y.m();
     var z := new Z.C;
     z.m();
   }
}

method NotMain() {
  A.run();
}


abstract module S1 {
  import B as S default T;
  static method do()
}

module T1 refines S1 {
  static method do() {
    var x := 3;
  }
}
module A1 {
   import X as S1 default T1;
   static method run() {
     X.do();
     var x := new X.B.C;
     x.m();
   }
}
