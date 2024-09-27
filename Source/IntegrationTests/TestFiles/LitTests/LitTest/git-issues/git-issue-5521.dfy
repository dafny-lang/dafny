// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

module WithoutWitnessClause {
  type Empty = x: int | false witness *

  newtype NewEmpty = Empty // error: the default-witness 0 is not a witness

  method OperateOnNewEmpty(x: NewEmpty)
    ensures false
  {
    var y: Empty := x as Empty;
  }

  method Test() {
    var x: NewEmpty := *;
    OperateOnNewEmpty(x);
    print 10 / 0;
  }
}

module WithWitnessClause {
  type Empty = x: int | false witness *

  newtype NewEmpty = Empty witness 506 // error: 506 is not a witness

  method OperateOnNewEmpty(x: NewEmpty)
    ensures false
  {
    var y: Empty := x as Empty;
  }

  method Test() {
    var x: NewEmpty := *;
    OperateOnNewEmpty(x);
    print 10 / 0;
  }
}

module WithGhostWitnessClause {
  type Empty = x: int | false witness *

  newtype NewEmpty = Empty ghost witness 506 // error: 506 is not a ghost witness

  method OperateOnNewEmpty(x: NewEmpty)
    ensures false
  {
    var y: Empty := x as Empty;
  }

  method Test() {
    var x: NewEmpty := *;
    OperateOnNewEmpty(x); // error: x is used before it has really been initialized
    print 10 / 0;
  }
}

module DeclaredAsPossiblyEmpty {
  type Empty = x: int | false witness *

  newtype NewEmpty = Empty witness *

  method OperateOnNewEmpty(x: NewEmpty)
    ensures false
  {
    var y: Empty := x as Empty;
  }

  method Test() {
    var x: NewEmpty := *;
    OperateOnNewEmpty(x); // error: x is used before it has really been initialized
    print 10 / 0;
  }
}
