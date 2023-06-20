// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

datatype obj = Obj(fooBar:map<foo,int>)
datatype foo = Foo

method test_case() returns (o:obj)
{
    if true {
        o:= o.(fooBar := o.fooBar[Foo := 3]);
    }
}

method Main() {
  var o := test_case();
  if Foo in o.fooBar {
    print o.fooBar[Foo], "\n";  // 3
  }
  var m: map<foo,int>;
}
