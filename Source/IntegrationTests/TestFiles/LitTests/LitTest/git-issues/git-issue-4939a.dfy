// RUN: %exits-with 4 %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module FromIssue0 {
  trait Program {
    method Compute() returns (r: Result)
  }

  datatype Result =
    | Bounce(next: Program)
    | Done()

  datatype Trivial extends Program =
    Trivial()
  {
    method Compute() returns (r: Result) {
      return Done();
    }
  }

  datatype Seq extends Program =
    Seq(left: Program, right: Program) // this once gave an error, saying Seq is empty because of cyclic dependencies
  {
    method Compute() returns (r: Result) {
      var result := left.Compute(); // error: cannot prove termination
      match result
      case Done() => r := right.Compute();
      case Bounce(next) =>
        var next' := Seq(next, right);
        assert next' is Program;
        return Bounce(next');
    }
  }
}

module FromIssue1 {
  trait Program {
  }

  datatype Trivial extends Program =
    Trivial()

  datatype Seq extends Program =
    Seq(left: Program, right: Program) // this once gave an error, saying Seq is empty because of cyclic dependencies
}

module FromIssue2 {
  // NoInstances has no instances
  class NoInstances {
    constructor ()
      requires false
    {
    }
  }

  // ... and therefore, neither does D. However, this is not detected syntactically, so there are no complaints.
  datatype D = D(n: NoInstances)
}

module FromIssue3 {
  trait Interface {
    function getString(i: int): string
  }

  datatype Wrapper extends Interface = Wrapper(inner: Interface) // this once gave the cyclic-dependency error
  {
    function getString(i: int): string {
      inner.getString(i + 1) // error: cannot prove termination
    }
  }

  datatype DetectZero extends Interface  = DetectZero
  {
    function getString(i: int): string {
      if i == 0
      then "zero"
      else "I don't know"
    }
  }

  function getWrappedDetectZero(): Interface {
    Wrapper(DetectZero)
  }
}

module FromIssue4 {
  trait Interface {
    function GetString(i: int): string
  }

  class {:extern} Store {
    var interface: Interface

    constructor (interface: Interface) {
      this.interface := interface;
    }

    function GetInterface(): (res: Interface)
       ensures res == interface
  }

  datatype Wrapper extends Interface = Wrapper(inner: Store)
  {
    function GetString(i: int): string {
      inner.GetInterface().GetString(i + 1) // error: cannot prove termination
    }
  }
}

module SimpleExample0 {
  trait GeneralTrait {
  }

  datatype Wrapper = Wrapper(g: GeneralTrait) // this once gave the cyclic-dependency error
}

module SimpleExample1 {
  trait ReferenceTrait extends object {
  }

  datatype Wrapper = Wrapper(g: ReferenceTrait) // this was always fine
}

module Standard {
  datatype List<X> = Nil | Cons(X, List<X>)

  datatype Op = Plus | Times
  datatype Expr = Value(int) | Node(operator: Op, arguments: List<Expr>)
}

module Good0 {
  datatype Mutual = M0(Nutual) | M1(Mutual)
  datatype Nutual = N0(Mutual) | Easy
}

module Good1 {
  datatype Nutual = N0(Mutual) | Easy
  datatype Mutual = M0(Nutual) | M1(Mutual)
}

module Bad {
  datatype T = Make(T, T) // warning: empty datatype

  datatype Mutual = M0(Nutual) | M1(Mutual) // warning: empty datatype
  datatype Nutual = N0(Mutual) // warning: empty datatype
}

// The following module contains tests for some previous boxing translation errors
module RegressionTest {
  trait Interface { }

  datatype Wrapper = Wrapper(inner: Interface)

  method Test0(ww: Wrapper) {
    var w: Wrapper;
    w := ww as Wrapper;
  }

  method Test1(i: Interface) {
    var w: Wrapper;
    w := Wrapper(i) as Wrapper;
  }

  predicate P(x: int) { true }

  method Test() returns (ghost h: bool)  {
    h := forall i: int :: P(i) ==> var j: int :| true; false;
  }
}

// The following module also contains tests for some previous boxing translation errors
module OtherRegressionTests {
  trait Parent extends object { }
  class MyClass extends Parent { }

  datatype Brapper = Brapper(inner: Parent)

  method Testx(c: MyClass) {
    var kw :=
      var jj: Parent := c;
      Brapper(jj);
    assert true;
  }

  // ----

  trait Interface { }

  datatype Wrapper extends Interface = Wrapper(inner: Interface)

  datatype DetectZero extends Interface  = DetectZero

  function getWrappedDetectZero(): Interface {
    var i: Interface := DetectZero;
    var w: Wrapper := Wrapper(i);
    w
  }

  method Test(w: Wrapper) returns (i: Interface) {
    i := w;
    i :=
      var k: Wrapper := Wrapper(i);
      k;
    var j: Interface :=
      var i: Interface := DetectZero;
      var w: Wrapper := Wrapper(i);
      w;
  }

  method SameTest() returns () {
    var ui: Interface := DetectZero;
    var e := Wrapper(ui);

    var kw :=
      var jj: Interface := DetectZero;
      Wrapper(jj);

    assert true;
  }
}
