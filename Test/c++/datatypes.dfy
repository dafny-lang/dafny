newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000

datatype Example1 = Example1(u:uint32, b:bool)
datatype Example2 = Ex2a(u:uint32) | Ex2b(b:bool)
datatype Example3 = Example3(e:Example1)

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

method Main() {
    var e1 := Example1(22, false);
    var e2 := Ex2a(42);
    Callee(e2);
    e2 := Ex2b(true);
    Callee(e2);
}

datatype Option<V> = None | Some(value:V)

datatype Err<V> = Fail(err:bool) | Ok(value:V)


method matcher(e:Err<uint32>) {
  match e 
    case Fail(s) => print s;
    case Ok(v) => print v;
}

method GenericTest() {
  var v:Option<uint32> := Some(32);
  matcher(Ok(42));
  matcher(Fail(true));
}
