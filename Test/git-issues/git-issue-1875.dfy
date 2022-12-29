// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/// This file checks whether sufficient axioms are generated to compare
/// datatypes constructed using subset types over sequences.

module Datatype {
  datatype Box_<T> = Box(t: T)
  type Box<T> = b: Box_<T> | true witness *

  datatype List<T> = Nil | Cons(t: T, Box<List<T>>)

  function Length<T>(l: List<T>): int {
    match l {
      case Nil => 0
      case Cons(t, q) => 1 + Length(q.t)
    }
  }
}

module Seq {
  type Box_<T> = seq<T>
  type Box<T> = b: Box_<T> | |b| == 1 witness *

  datatype List<T> = Nil | Cons(t: T, Box<List<T>>)

  function Length<T>(l: List<T>): int {
    match l {
      case Nil => 0
      case Cons(t, q) =>
        assert q[0] in q;
        var l :| l in q;
        Length(l)
    }
  }
}

module Set {
  type Box_<T> = set<T>
  type Box<T> = b: Box_<T> | |b| == 1 witness *

  datatype List<T(==)> = Nil | Cons(t: T, Box<List<T>>)

  function Length<T>(l: List<T>): int {
    match l {
      case Nil => 0
      case Cons(t, q) =>
        var l :| l in q;
        Length(l)
    }
  }
}

module Multiset {
  type Box_<T> = multiset<T>
  type Box<T> = b: Box_<T> | |b| == 1 witness *

  datatype List<T(==)> = Nil | Cons(t: T, Box<List<T>>)

  function Length<T>(l: List<T>): int {
    match l {
      case Nil => 0
      case Cons(t, q) =>
        var l :| l in q;
        Length(l)
    }
  }
}

module Map {
  type Box_<T> = map<T, bool>
  type Box<T> = b: Box_<T> | |b| == 1 witness *

  datatype List<T(==)> = Nil | Cons(t: T, Box<List<T>>)

  function Length<T>(l: List<T>): int {
    match l {
      case Nil => 0
      case Cons(t, q) =>
        var l :| l in q.Keys;
        Length(l)
    }
  }
}
