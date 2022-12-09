// RUN: %exits-with 2 %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The code in this file demonstrates how correct compilation of some features
// would require run-time type tests beyond what is reasonable to do at run time.
// In more detail, the problem occurs when a type test is needed to distinguish
// between Dafny types whose target representation is the same.  For example, the
// types "MyClass<int>" and "MyClass<nat>" are represented in the same way at
// run time, yet there are Dafny values that satisfy the former and not the latter.

class MyClass<A(0)> {
  var a: A
}

method M(s: set<object>) returns (t: set<MyClass<nat>>)
  ensures t <= s
{
  t := set x: MyClass<nat> | x in s;  // error: this must not be compilable
}

method N()
{
  var x := new MyClass<int>;
  x.a := -7;
  var y := new MyClass<nat>;
  y.a := 7;
  var o: set<object> := {x};
  o := o + {y};
  var t := M(o);
  assert forall z: MyClass<nat> :: z in t ==> 0 <= z.a;
  while |t| != 0
  {
    var u: MyClass<nat> :| u in t;
    assert 0 <= u.a;
    print u.a, "\n";
    t := t - {u};
  }
}

trait Tr { var u: int }

class Class0 extends Tr { var x: int }

class Class1 extends Tr { var y: real }

method O()
{
  var c0 := new Class0;
  var c1 := new Class1;
  var s: set<Tr> := {c0, c1};
  var t := set cc: Class1 | cc in s;  // this is fine
  while |t| != 0
  {
    var u: Class1 :| u in t;
    print u.y, "\n";
    t := t - {u};
  }
}

method Main()
{
  N();
  O();
}
