// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Basic {
  type MyType<A> = int

  type Int = int

  type PairaBools = (bool, bool)

  datatype List<T> = Nil | Cons(T, List)

  type Synonym0<T,U> = List<T>

  type Synonym1<T> = List  // type argument of List filled in automatically

  type Synonym2<A> = List<A>

  type Synonym3<B> = Synonym4

  type Synonym4<C> = Synonym2<C>

  type Synonym5<A,B> = List

  function Plus(x: Int, y: int): Int
  {
    x + y
  }

  method Next(s: Synonym1) returns (u: Synonym1)
  {
    match s
    case Nil => u := Nil;
    case Cons(_, tail) => u := tail;
  }

  method Add<W>(t: W, s: Synonym1) returns (u: Synonym1)
  {
    u := Cons(t, Nil);
  }

  function Skip(s: Synonym3): Synonym0
  {
    match s
    case Nil => Nil
    case Cons(_, tail) => tail
  }

  type MyMap = map<int, map<real, bool>>

  predicate MyMapProperty(m: MyMap, x: int)
  {
    x in m && x as real in m[x] && m[x][x as real]
  }
}

// --------------- Test knowledge of emptiness ---------------

module Library {
  export
    reveals Empty
  export Opaque
    provides Empty

  type Empty = x: int | false witness *
}

module KnowsItIsEmpty {
  import L = Library
  method M(x: L.Empty) {
    assert false;  // no prob, since L.Empty is known to be empty
  }
}

module OnlySeesOpaqueType {
  import L = Library`Opaque
  method M(x: L.Empty) {
    assert false;  // error
  }
}

// --------------- Test lack of knowledge of nonemptiness ---------------

module NonemptyLibrary {
  export E0
    reveals Something, A, B, C
  export E1
    provides Something
    reveals A, B, C
  export E2
    reveals Something
    provides A, B, C
  export E3
    provides Something, A, B, C
  export E4
    provides A, B, C

  type Something = int
  type A = Something
  type B(00) = Something
  type C(0) = Something
}

module ClientE0 {
  import L = NonemptyLibrary`E0
  method MethodS() returns (x: L.Something, ghost y: L.Something) {
  }
  method MethodA() returns (x: L.A, ghost y: L.A) {
  }
  method MethodB() returns (x: L.B, ghost y: L.B) {
  }
  method MethodC() returns (x: L.C, ghost y: L.C) {
  }
}

module ClientE1 {
  import L = NonemptyLibrary`E1
  method MethodS() returns (x: L.Something, ghost y: L.Something) {
  } // error (x2): x, y have not been assigned
  method MethodA() returns (x: L.A, ghost y: L.A) {
  } // error (x2): x, y have not been assigned
  method MethodB() returns (x: L.B, ghost y: L.B) {
  } // error (x2): x, y have not been assigned
  method MethodC() returns (x: L.C, ghost y: L.C) {
  } // error (x2): x, y have not been assigned
}

module ClientE2 {
  import L = NonemptyLibrary`E2
  method MethodS() returns (x: L.Something, ghost y: L.Something) {
  }
  method MethodA() returns (x: L.A, ghost y: L.A) {
  } // error (x2): x, y have not been assigned
  method MethodB() returns (x: L.B, ghost y: L.B) {
  } // error: x has not been assigned
  method MethodC() returns (x: L.C, ghost y: L.C) {
  }
}

module ClientE3 {
  import L = NonemptyLibrary`E3
  method MethodS() returns (x: L.Something, ghost y: L.Something) {
  } // error (x2): x, y have not been assigned
  method MethodA() returns (x: L.A, ghost y: L.A) {
  } // error (x2): x, y have not been assigned
  method MethodB() returns (x: L.B, ghost y: L.B) {
  } // error: x has not been assigned
  method MethodC() returns (x: L.C, ghost y: L.C) {
  }
}

module ClientE4 {
  import L = NonemptyLibrary`E4
  method MethodA() returns (x: L.A, ghost y: L.A) {
  } // error (x2): x, y have not been assigned
  method MethodB() returns (x: L.B, ghost y: L.B) {
  } // error: x has not been assigned
  method MethodC() returns (x: L.C, ghost y: L.C) {
  }
}
