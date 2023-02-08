// RUN: %testDafnyForEachCompiler "%s"

module {:options "--function-syntax=4"} Stacks {
  export
    reveals Stack
    provides Stack.Valid, Stack.Repr, Stack.Elements
    reveals Stack.Count
    provides Stack.Push, Stack.Pop

  datatype MaybeInitialized<T> = ghost Uninitialized | Initialized(value: T)

  // Note, nothing is assumed about the type parameter T in the following line. In particular,
  // it's not assumed to be an auto-init type (and, in fact, may even be empty).
  class Stack<T> {
    ghost var Repr: set<object>
    ghost var Elements: seq<T>
    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      arr in Repr &&
      n == |Elements| <= arr.Length != 0 &&
      forall i :: 0 <= i < n ==>
        arr[i].Initialized? && arr[i].value == Elements[i]
    }

    var arr: array<MaybeInitialized<T>>
    var n: nat

    constructor ()
      ensures Valid() && fresh(Repr) && Elements == []
    {
      Elements, n := [], 0;
      arr := new [20];
      Repr := {this, arr};
    }

    ghost function Count(): nat
      requires Valid()
      reads Repr
    {
      |Elements|
    } by method {
      return n;
    }

    method Push(t: T)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures Elements == old(Elements) + [t]
    {
      if n == arr.Length {
        var a := new [2 * n];
        forall i | 0 <= i < n {
          a[i] := arr[i];
        }
        arr := a;
        Repr := Repr + {a};
      }
      arr[n] := Initialized(t);
      Elements, n := Elements + [t], n + 1;
    }

    method Pop() returns (t: T)
      requires Valid() && Elements != []
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures var last := |old(Elements)| - 1;
        t == old(Elements)[last] &&
          Elements == old(Elements)[..last]
    {
      n := n - 1;
      Elements := Elements[..n];
      t := arr[n].value;
    }
  }
}

type Empty = x: int | false witness *

method Main() {
  var s := new Stacks.Stack();
  s.Push(10);
  s.Push(12);
  s.Push(11);
  var x := s.Pop();
  assert s.Elements == [10, 12] && x == 11;
  var count := s.Count();
  assert count == 2;
  print x, " ", count, "\n"; // 11 2

  var s' := new Stacks.Stack<Empty>();
  count := s'.Count();
  assert count == 0;
  print count, "\n"; // 0

  EnumerationTests.Test();
  DestructorTests.Test();

  Arrays.Test();
}

module {:options "/functionSyntax:4"} EnumerationTests {
  datatype Enum = ghost EnumA | EnumB
  {
    const N := 13

    ghost predicate Is(n: nat) {
      N == n
    }
  }

  datatype AllGhost = ghost Ctor0 | ghost Ctor1
  {
    const N := 13

    ghost predicate Is(n: nat) {
      N == n
    }

    method CheckIs(n: nat) returns (r: bool) {
      r := N == n;
    }
  }

  method Test() {
    var e := PickEnumValue();
    var s: seq<Enum>;
    s := [e];
    print |s|, "\n"; // 1

    var g, sg;
    g := PickAllGhostValue();
    sg := [g];
    print |sg|, "\n"; // 1
  }

  method PickEnumValue() returns (r: Enum) {
    if e: Enum :| e.Is(13) {
      r := e;
    }
  }

  method PickAllGhostValue() returns (r: AllGhost) {
    if ag: AllGhost :| ag.Is(13) {
      r := ag;
    }
  }
}

module {:options "/functionSyntax:4"} DestructorTests {
  datatype WithCommonDestructors<A, B> =
    | CtorA(a: A, x: int)
    | ghost CtorAB(a: A, b: B)
    | CtorB(b: B, y: int, ghost z: int)

  method Test() {
    var wcd := CtorA(true, 7);
    print wcd.a, " "; // true
    wcd := wcd.(a := false);
    print wcd.a, " ", wcd.x, "\n"; // false 7

    wcd := CtorB(2.11, 9, 100);
    print wcd.b, " "; // 2.11
    wcd := wcd.(b := 2.13);
    print wcd.b, " ", wcd.y, "\n"; // 2.13 9

    wcd := wcd.(y := 11, z := 101);
    print wcd.y, " "; // 11
    wcd := wcd.(z := 102, y := 12);
    print wcd.y, " "; // 12
    wcd := wcd.(z := 103);
    print wcd.y, "\n"; // 12
  }
}

module {:options "/functionSyntax:4"} WhiteBoxTests {
  // The following code tests two conditions in the implementation.

  // The following List does not support equality (because of the ghost parameter)
  datatype List = Nil | Nilly(x: int) | Konstig(ghost head: int, tail: List)
  type RestrictedList = xs: List | xs == Nilly(2) witness *

  method M(xs: RestrictedList) returns (b: bool) {
    // "Resolver.CanCompareWith" returns "true" for the LHS in the following comparison
    // and returns "false" for the RHS. This shows that one needs to call "Resolver.CanCompareWith"
    // on both operands. If either of them returns true, the comparison can be compiled.
    // Additionally, since the type of "xs" is a subset type, this test makes sure that
    // "PartiallySupportsEquality" understands subset types.
    b := xs == Nilly(2);
  }
}

module ConstraintsAreGhost {
  // The constraint of a subset type is ghost. However, the Resolver calls CheckIsCompilable
  // to determine if, perhaps, the constraint is compilable after all (because that enables
  // the compiler to do some additional things). The .InCompiledContext fields should not be
  // set when CheckIsCompilable is called in this mode, as is tested by the following declarations.

  datatype A = ghost MakeA(x: int)
  type B = a: A | a.x == 0 ghost witness MakeA(0)

  datatype R = R(ghost x: int)
  type S = r: R | r.x == 0 witness R(0)

  datatype List = Nil | ghost Konstig(ghost head: int, tail: List)
  type RestrictedList = xs: List | xs.Konstig? ghost witness Konstig(0, Nil)
}

module Arrays {
  datatype MaybeInitialized<T> = ghost Uninitialized | Initialized(value: T)
  datatype Singleton<X> = Single(X)

  type Synonym = MaybeInitialized<Class>
  class Class { }

  method Test() {
    M<bv5>();

    var st := new Stack(5 as bv5);
    st.U(6);
    Print(st.arr, " | ");
    Print(st.trr, " | ");
    Print(st.brr, "\n");
  }

  method M<T>() {
    var arr := new MaybeInitialized<T>[20]; // no need to initialize the array at run time
    var srr := new Singleton<MaybeInitialized<T>>[20]; // no need to initialize the array at run time
    var yrr := new Synonym[20]; // no need to initialize the array at run time
    var trr := new (ghost bool, ghost real, Singleton<MaybeInitialized<T>>, ghost int)[20]; // no need to initialize the array at run time
    print arr.Length + srr.Length + yrr.Length + trr.Length, "\n"; // 80
  }

  method Print<X>(x: array<X>, suffix: string) {
    if x.Length != 0 {
      print x[x.Length / 2], suffix;
    }
  }

  class Stack<T> {
    var arr: array<MaybeInitialized<T>>
    var trr: array<T>
    var brr: array<bool>
    var arr2: array2<MaybeInitialized<T>>
    var trr2: array2<T>
    var brr2: array2<bool>

    constructor (t: T)
      ensures fresh(arr) && fresh(trr) && fresh(brr)
    {
      arr := new [20];
      trr := new [20](_ => t);
      brr := new [20];
    }
    method U(t: T)
      modifies this, arr, trr, brr
    {
      arr := Update(arr, Initialized(t));
      trr := Update(trr, t);
      brr := Update(brr, true);
    }
  }

  method Update<T>(a: array<T>, t: T) returns (r: array<T>)
    modifies a
  {
    if a.Length != 0 {
      a[a.Length / 2] := t;
    }
    r := a;
  }
}
