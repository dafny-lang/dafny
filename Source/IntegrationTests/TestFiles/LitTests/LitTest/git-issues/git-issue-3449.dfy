// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


class Basic { }

method Test()
{
  // "new object" allocates an object of an abitrary type
  var obj: object := new object;
  if * {
    assert !(obj is Basic); // error: no reason to think obj couldn't be a Basic
  } else {
    assert !(obj is array<int>); // error: no reason to think obj couldn't be an array<int>
  }
}
