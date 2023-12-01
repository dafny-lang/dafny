// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


class MyClass {
  ghost const repr: object
  constructor (ghost r: object) {
    repr := r;
  }
}

datatype D1 = D1(o: MyClass)
{
  ghost const objs: set<object> := getObjs()  // Error

  ghost function getObjs(): set<object>
    reads o
  {
    {o, o.repr}
  }
}

class MyClass2 {
  var x: int
  const c := F() // Error

  function F(): int
    reads this
  {
    x
  }
}
