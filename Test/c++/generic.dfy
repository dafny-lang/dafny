
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

method Main() {
  var t := new Test(true);
  var u := new UseTest();
  u.DoSomething(t);
}
