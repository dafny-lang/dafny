// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp /unicodeChar:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = i:int | 0 <= i < 0x100000000

datatype Op =
  | NoOp
  | PushOp(ghost id: int)

datatype Example1 = Example1(u:uint32, b:bool)
datatype Example2 = Ex2a(u:uint32) | Ex2b(b:bool)
datatype Example3 = Example3(e:Example1)
datatype Example4 = Ex4a | Ex4b
datatype Example5<V> = Ex5a(v:V) | Ex5b(b:bool)
datatype Example6 = Ex6a(u:uint32) | Ex6b(b:bool) | Ex6c(u:uint32, s:seq<bool>)
type Ex1Sub = d:Example1 | d.u == 0 witness Example1(0, true)
type Ex2Sub = d:Example2 | d.Ex2a? && d.u == 0 witness Ex2a(0)
type Ex3Sub = d:Example3 | d.e.b witness Example3(Example1(42, true))

datatype DtPointer = DtPointer(s:seq<uint32>)
datatype DtPointerHolder = DtPointerHolder(e:DtPointer) | Other(f:bool)

method Matcher(e:Example1) {
  match e {
    case Example1(u, b) => print u, b;
  }
}

method TupleMatch(e1:Example2, e2:Example2) {
  match (e1, e2) {
    case (Ex2a(u1), Ex2a(u2)) => print u1, u2, "\n";
    case (Ex2b(u1), Ex2a(u2)) => print u1, u2, "\n";
    case (Ex2a(u1), Ex2b(u2)) => print u1, u2, "\n";
    case (Ex2b(u1), Ex2b(u2)) => print u1, u2, "\n";
  }
}

method Callee(e:Example2) {
  match e {
    case Ex2a(u) => print "Case A: ", u, "\n";
    case Ex2b(b) => print "Case B: ", b, "\n";
  }
}

method DtUpdate(e:Example1)
{
  var x := e.(u := 0);
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

method TestGenericDefault() {
  var x:Option<Example5<bool>>;
}

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


datatype Dup = Dup1(b:bool, x:uint32) | Dup2(x:uint32)

method DupTest(d:Dup)
{
  var y := d.x;
  print y;
  print "\n";
}

method DupTestTest()
{
  DupTest(Dup1(false, 42));
  DupTest(Dup2(330));
}

datatype IntList =
  | Nil
  | Cons(hd:uint32, tl:IntList)

method IntListLen(l:IntList) returns (len:uint32)
{
  match l {
    case Nil => len := 0;
    case Cons(hd, tl) =>
      var len_rest := IntListLen(tl);
      if len_rest < 0xFFFFFFFF {
        len := len_rest + 1;
      } else {
        len := len_rest;
      }
  }
}

// Test generic datatype methods
datatype Foo<A> = Foo(a: A) {
  static method Alloc(a: A) returns (f: Foo<A>) {
    f := Foo(a);
  }
}

datatype Test<A> = Test(a:A) | Empty
{
  static method Alloc() returns (t:Test<A>) {
    return Empty;
  }

  static method Invoke() {
    var a := Alloc();
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
  DupTestTest();

  var len := IntListLen(Cons(15, Cons(18, Cons(330, Nil))));
  print len, "\n";
}

