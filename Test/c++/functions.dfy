newtype{:nativeType "uint"} uint32  = i:int | 0 <= i < 0x100000000
newtype{:nativeType "ulong"} uint64 = i:int | 0 <= i < 0x10000000000000000

function method Test(x:uint32) : uint64 {
  x as uint64 + 1
}

function method Seqs<T>(s:seq<T>, x:uint32, default_val:T) : T 
  requires |s| < 1000;
{
  if |s| as uint32 > x then s[x] else default_val
}


method Main() {
  var y := Test(12);
}
