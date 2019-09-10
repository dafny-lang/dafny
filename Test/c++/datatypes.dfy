newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000

datatype Example1 = Example1(u:uint32, b:bool)
datatype Example2 = Ex2a(u:uint32) | Ex2b(b:bool)

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

