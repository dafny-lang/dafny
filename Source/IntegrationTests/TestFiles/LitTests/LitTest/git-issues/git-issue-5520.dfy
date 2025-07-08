// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

module SubsetTypeSubsetType {
  type Empty = x: int | false witness *

  method OperateOnEmpty(x: Empty)
    ensures false
  {
  }

  type PurportsToBeNonempty = x: Empty | true
    witness 506 // error: this is not a witness

  method Test() {
    var x: PurportsToBeNonempty := *;
    OperateOnEmpty(x);
    print 10 / 0;
  }
}

module SubsetTypeNewtype {
  type Empty = x: int | false witness *

  newtype PurportsToBeNonempty = x: Empty | true
    witness 506 // error: this is not a witness

  method OperateOnEmpty(x: PurportsToBeNonempty)
    ensures false
  {
  }

  method Test() {
    var x: PurportsToBeNonempty := *;
    OperateOnEmpty(x);
    print 10 / 0;
  }
}

module NewtypeSubsetType {
  type Empty = x: int | false witness *

  method OperateOnEmpty(x: Empty)
    ensures false
  {
  }

  type PurportsToBeNonempty = x: Empty | true
    witness 506 // error: this is not a witness

  method Test() {
    var x: PurportsToBeNonempty := *;
    OperateOnEmpty(x);
    print 10 / 0;
  }
}

module NewtypeNewtype {
  type Empty = x: int | false witness *

  newtype PurportsToBeNonempty = x: Empty | true
    witness 506 // error: this is not a witness

  method OperateOnEmpty(x: PurportsToBeNonempty)
    ensures false
  {
  }

  method Test() {
    var x: PurportsToBeNonempty := *;
    OperateOnEmpty(x);
    print 10 / 0;
  }
}
