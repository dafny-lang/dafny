import opened DafnyStdLibs.BoundedInts

method BoundedIntUser(x: uint32, z: nat16) {

  assert TWO_TO_THE_15 * 2 == TWO_TO_THE_16;

  assert 0 <= (x as int) < TWO_TO_THE_32;
  var y: uint64 := x as int as uint64;
  var int16 := z as int as int16;
  var uint16 := z as int as uint16;
  
  // Nat can be converted to int without a cast
  var nat234: nat16 := 234;
  var int234 := nat234;
}
