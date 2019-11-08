newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000

datatype Op =
  | NoOp
  | PushOp(ghost id: int)

datatype Example1 = Example1(u:uint32, b:bool)
datatype Example2 = Ex2a(u:uint32) | Ex2b(b:bool)
datatype Example3 = Example3(e:Example1)
datatype Example4 = Ex4a | Ex4b

type Ex1Sub = d:Example1 | d.u == 0 witness Example1(0, true)
type Ex2Sub = d:Example2 | d.Ex2a? && d.u == 0 witness Ex2a(0)
type Ex3Sub = d:Example3 | d.e.b witness Example3(Example1(42, true))

datatype DtPointer = DtPointer(s:seq<uint32>)
datatype DtPointerHolder = DtPointerHolder(e:DtPointer) | Other(f:bool)

method Callee(e:Example2) {
    match e {
        case Ex2a(u) => print "Case A: ", u, "\n";
        case Ex2b(b) => print "Case B: ", b, "\n";
    }
}

method TestDestructor() {
    var e1 := Example1(22, false);
    var x := e1.u;
    if x == 22 {
      print "This is expected\n";
    } else {
      assert false;
      print "This is unexpected!!!\n";
    }
}


datatype Option<V> = None | Some(value:V)
datatype Err<V> = Fail(err:bool) | Ok(value:V)


method matcher(e:Err<uint32>) {
  match e {
    case Fail(s) => print s;
    case Ok(v) => print v;
  }
  print "\n";
}

method GenericTest() {
  var v:Option<uint32> := Some(32);
  matcher(Ok(42));
  matcher(Fail(true));
  if v.Some? { print "Got some:", v.value, "\n"; }
}

method Comparison(x0:Example1, x1:Example1, y0:Example4, y1:Example4) {
  if x0 == x1 {
    print "Example1s are equal\n";
  }
  if x0 != x1 {
    print "Example1s are not equal\n";
  }
  if y0 == y1 {
    print "Example4s are equal\n";
  }
  if y0 != y1 {
    print "Example4s are not equal\n";
  }
}

method Main() {
    var e1 := Example1(22, false);
    var e2 := Ex2a(42);
    Callee(e2);
    e2 := Ex2b(true);
    Callee(e2);
    TestDestructor();
    GenericTest();
    Comparison(Example1(42, true), Example1(42, true), Ex4b, Ex4b);
    Comparison(Example1(42, false), Example1(42, true), Ex4a, Ex4a);
    Comparison(Example1(2,  false), Example1(42, false), Ex4a, Ex4b);
}
