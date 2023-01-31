// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass {
  ghost const repr: object
  constructor (ghost r: object) {
    repr := r;
  }
}

datatype D1 = D1(o: MyClass)
{
  ghost const objs: set<object> := getObjs()  // Error

  function getObjs(): set<object>
    reads o
  {
    {o, o.repr}
  }
}

class MyClass2 {
  var x: int
  const c := F() // Error

  function method F(): int
    reads this
  {
    x
  }
}
