// RUN: %exits-with 2 %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
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
      var result := left.Compute();
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
      inner.getString(i+1)
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
      inner.GetInterface().GetString(i + 1)
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
  datatype T = Make(T, T) // error: obviously empty

  datatype Mutual = M0(Nutual) | M1(Mutual) // error: empty
  datatype Nutual = N0(Mutual) // error: empty
}
