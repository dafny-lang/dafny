
newtype{:nativeType "uint"} uint32 = i:int | 0 <= i < 0x100000000

method ReturnTuple() returns (x:(uint32,uint32))
{
  return (1, 2);
}

method Main() {
  var x := ReturnTuple();
  var y := x.0;
}
