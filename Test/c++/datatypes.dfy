//newtype{:nativeType "sbyte"} sbyte = i:int | -0x80 <= i < 0x80
//newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100
//newtype{:nativeType "short"} int16 = i:int | -0x8000 <= i < 0x8000
//newtype{:nativeType "ushort"} uint16 = i:int | 0 <= i < 0x10000
//newtype{:nativeType "int"} int32 = i:int | -0x80000000 <= i < 0x80000000
newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000
//newtype{:nativeType "long"} int64 = i:int | -0x8000000000000000 <= i < 0x8000000000000000
//newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000
//newtype{:nativeType "sbyte"} nat8 = i:int | 0 <= i < 0x80
//newtype{:nativeType "short"} nat16 = i:int | 0 <= i < 0x8000
//newtype{:nativeType "int"} nat32 = i:int | 0 <= i < 0x80000000
//newtype{:nativeType "long"} nat64 = i:int | 0 <= i < 0x8000000000000000

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
