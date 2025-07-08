// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --print-ranges


// ------------------- infer array types for Indexable and MultiIndexable XConstraints ----------
// ------------------- using weaker subtyping constraints                              ----------

module AdvancedIndexableInference {
  datatype MyRecord = Make(x: int, y: int)

  method M(d: array<MyRecord>, e: seq<MyRecord>)
    requires d.Length == 100 == |e|
  {
    if * {
      var c := d;
      var xx := c[25].x;
    } else if * {
      var c := d;
      var xx := c[25..50][10].x; // Unfortunately, this gives an error with the new resolver, because it doesn't see to get the element type of c[25..50]
                                // The best way to improve this is to make name lookups be GuardedConstraints in the resolver, so this may change in the future.
    } else if * {
      var c := e;
      var xx := c[25].x;
    } else {
      var c := e;
      var xx := c[25..50][10].x;
    }
  }
}
// --------------------------

module TypeConversions {
  trait J extends object { }
  class C extends J { }

  method M() returns (x: int, n: nat, o: object, j: J, c: C) {
    n := x as nat;  // yes, this is allowed now
    o := j;
    j := o;  // OK for type resolution, but must be proved (new resolver: error, because it requires an explicit cast here)
    j := o as J;  // yes, this is allowed now
    j := c;
    c := j;  // OK for type resolution, but must be proved (new resolver: error, because it requires an explicit cast here)
    c := j as C;  // yes, this is allowed now
    var oo := o as realint;  // error: there's no such type as "realint" (this once used to crash Dafny)
  }
}

// --------------------- regression

module Regression_NewType {
  class C { }
  newtype MyInt = x: int | {} == set c: C | c  // this once crashed Dafny
}

// --------------------- regression

module PrefixGeneratorDuplicates {
  greatest predicate P()
  greatest predicate P()  // error: duplicate name (this once crashed Dafny)
  greatest lemma L()
  greatest lemma L()  // error: duplicate name (this once crashed Dafny)
}

// ------------------- unary TLA+ style predicates -------------------

module TLAplusOperators {
  ghost function BadA(y: int): int  // error: body has wrong return type
  {
    && 5 + y  // error: using operator "&&" requires the operand to be boolean
  }

  ghost function BadB(y: int): bool
  {
    && 5 + y  // error: using operator "&&" requires the operand to be boolean
  }

  ghost function BadC(y: int): int  // error: body has wrong return type
  {
    || 5 + y  // error: using operator "||" requires the operand to be boolean
  }

  ghost function BadD(y: int): bool
  {
    || 5 + y  // error: using operator "||" requires the operand to be boolean
  }

  ghost function BadE(y: int): int  // error: body has wrong return type
  {
    && (|| 5 + y)  // error: bad types
  }
}

// ------------------------- divided constructors -------------------

module DividedConstructors {
  class MyClass {
    var a: nat
    var b: nat
    var c: nat
    var n: MyClass
    const t := 17
    static const g := 25

    constructor Init(x: nat)
    {
      this.a := this.b;  // this use of "this" in RHS is allowed
      ((this)).b := 10;
      n := new MyClass();
      n.a := 10;  // error: not allowed use of "this" in this way
      c := a + b;  // error (x2): not allowed "this" in RHS
      var th := this;  // error: not allowed "this" in RHS
      Helper();  // error: not allowed to call instance method
      var mc := new MyClass();
      StaticHelper(mc);
      this.StaticHelper(mc);  // error: "this" is benign here; yet, it seems consistent to disallow it
      StaticHelper(this);  // error: cannot use "this" here
      P(a);  // error: cannot use "this" here
      P(g);
      P(this.g);  // error: "this" is benign here; yet, it seems consistent to disallow it
      modify this;  // error: cannot use "this" here
      modify this`c;  // error: cannot use "this" here
      modify `c;  // error: cannot use (implicit) "this" here
      new;
      a := a + b;
      Helper();
    }

    method Helper()
    {
    }

    static method StaticHelper(mc: MyClass)
    {
    }

    static method P(x: nat)
    {
    }

    constructor ()
    {
      a, c := 0, 0;
      new;
    }
  }
}

module ConstructorsThisUsage {
  class C {
    var x: int

    constructor M()
      requires this != null  // error: cannot use "this" here
      modifies this  // error: cannot use "this" here (but we just issue a deprecation warning)
      decreases this.x  // error: cannot use "this" here
      ensures this.x == 5
    {
      x := 5;
    }
  }
}

module ReturnBeforeNew {
  class C {
    var a: int
    var b: int

    constructor TriesToReturnBeforeNew(xyz: int)
    {
      a := 0;
      if xyz < 100 {
        return;  // error: "return" is not allowed before "new;"
      }
    }
  }
}

// ---------------- required auto-initialization -----------------------

module ZI {
  // the following are different syntactic ways of saying that the type
  // must support auto-initialization
  type ZA(0)
  type ZB(==)(0)
  type ZC(0)(==)
  type ZD(==,0)
  type ZE(0,==)
  type Y

  method P<G(0)>(x: G)

  method M0<F,G(0)>(a: ZA, b: ZB, c: ZC, d: ZD, e: ZE, f: F, g: G, y: Y)
  {
    P(a);
    P(b);
    P(c);
    P(d);
    P(e);
    P(f);  // error: type of argument is expected to support auto-initialization
    P(g);
    P(y);  // error: type of argument is expected to support auto-initialization
  }

  datatype List<T> = Nil | Cons(T, List<T>)

  method M1<G,H(0)>(xs: List<G>, ys: List<H>) {
    P(xs);  // yay, type of argument does support auto-initialization
    P(ys);  // yay, type of argument does support auto-initialization
  }

  class Cls {
    var q: int
    var rs: List<List<Cls>>
  }
  method M2(c: Cls?) {
    P(c);
  }

  newtype byte = x: int | 0 <= x < 256  // supports auto-initialization
  newtype MyInt = int  // supports auto-initialization
  newtype SixOrMore = x | 6 <= x ghost witness 6
  newtype AnotherSixOrMore = s: SixOrMore | true ghost witness 6
  newtype MySixOrMore = x: MyInt | 6 <= x ghost witness 6
  // The resolver uses the presence/absence of a "witness" clause to figure out if the type
  // supports auto-initialization.  This can be inaccurate.  If the type does not have a
  // "witness" clause, some type replacements may slip by the resolver, but will then be
  // caught by the verifier when the witness test is performed (because the witness test
  // uses a zero value in the absence of a "witness" clause).
  // A "ghost witness" clause tells the resolver that the type does not support
  // auto-initialization, but only ghost auto-initialzation.

  newtype UnclearA = x: int | true ghost witness 0  // actually supports auto-initialization, but has a "ghost witness" clause
  newtype UnclearB = x | x == 6 && x < 4  // "witness" clause omitted; type does not actually support auto-initialization

  method M3(a: byte, b: MyInt, c: SixOrMore, d: AnotherSixOrMore, e: MySixOrMore,
            ua: UnclearA, ub: UnclearB) {
    P(a);
    P(b);
    P(c);  // error: type of argument is expected to support auto-initialization
    P(d);  // error: type of argument is expected to support auto-initialization
    P(e);  // error: type of argument is expected to support auto-initialization
    P(ua);  // error: as far as the resolver can tell, type of argument does not support auto-initialization
    P(ub);  // fine, as far as the resolver can tell (but this would be caught later by the verifier)
  }

  type Sbyte = x: int | 0 <= x < 256  // supports auto-initialization
  type SMyInt = int  // supports auto-initialization
  type SSixOrMore = x | 6 <= x ghost witness 6
  type SAnotherSixOrMore = s: SSixOrMore | true ghost witness 6
  type SMySixOrMore = x: SMyInt | 6 <= x ghost witness 6
  type SUnclearA = x: int | true ghost witness 0  // see note about for UnclearA
  type SUnclearB = x | 6 <= x  // see note about for UnclearB

  method M4(a: Sbyte, b: SMyInt, c: SSixOrMore, d: SAnotherSixOrMore, e: SMySixOrMore,
            sua: SUnclearA, sub: SUnclearB) {
    P<Sbyte>(a);
    P<SMyInt>(b);
    P<SSixOrMore>(c);  // error: type of argument is expected to support auto-initialization
    P<SAnotherSixOrMore>(d);  // error: type of argument is expected to support auto-initialization
    P<SMySixOrMore>(e);  // error: type of argument is expected to support auto-initialization
    P<SUnclearA>(sua);  // error: as far as the resolver can tell, type of argument does not support auto-initialization
    P<SUnclearB>(sub);  // fine, as far as the resolver can tell (but this would be caught later by the verifier)
  }
}

abstract module ZI_RefinementAbstract {
  type A0
  type A1
  type A2
  type A3
  type B0(0)
  type B1(0)
  type B2(0)
  type B3(0)
  type C0(00)
  type C1(00)
  type C2(00)
  type C3(00)

  method Delta<Q(0),W,E(0),R>()
}

module ZI_RefinementConcrete0 refines ZI_RefinementAbstract {
  newtype Kuusi = x | 6 <= x witness 6  // supports auto-initialization
  newtype Six = x | 6 <= x ghost witness 6  // does not support auto-initialization
  newtype Sesis = x | 6 <= x witness *  // possibly empty
  type A0 = int
  type A1 = Kuusi
  type A2 = Six
  type A3 = Sesis
  type B0 = int
  type B1 = Kuusi
  type B2 = Six  // error: RHS is expected to support auto-initialization
  type B3 = Sesis  // error: RHS is expected to support auto-initialization
  type C0 = int
  type C1 = Kuusi
  type C2 = Six
  type C3 = Sesis  // error: RHS is expected to be nonempty
}

module ZI_ExportSource {
  export
    reveals RGB
    provides XYZ
  datatype RGB = Red | Green | Blue
  datatype XYZ = X | Y | Z
}

module ZI_RefinementConcrete1 refines ZI_RefinementAbstract {
  import Z = ZI_ExportSource

  method P<G(0)>(g: G)
  method M(m: Z.RGB, n: Z.XYZ) {
    P(m);
    P(n);  // error: Z.XYZ is not known to support auto-initialization
  }

  method Delta<
    Q,  // error: not allowed to change auto-initialization setting
    W,
    E(0),
    R(0)>()  // error: not allowed to change auto-initialization setting
}

module ZI_RefinementConcrete2 refines ZI_RefinementAbstract {
  type A0
  type A1(0)
  type A2(00)
  type B0      // error (with hint): not allowed to change auto-initialization setting from (0) to nothing
  type B1(0)
  type B2(00)  // error (with hint): not allowed to change auto-initialization setting from (0) to (00)
  type C0      // error (with hint): not allowed to change nonempty setting from (00) to nothing
  type C1(0)
  type C2(00)
}
