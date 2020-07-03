
class Test<T> {
  var t:T;

  constructor (e:T) {
    t := e;
  }
}

class UseTest<T> {
  constructor () {}
  method DoSomething(t:Test<T>)
  {
    var x:Test<T> := t;
  }
}


datatype Err<V> = Fail(b:bool) | Ok(value:V)
method ErrTest() returns (e:Err<bool>)
{
  return Fail(false);
}

method Main() {
  var t := new Test(true);
  var u := new UseTest();
  u.DoSomething(t);
}
