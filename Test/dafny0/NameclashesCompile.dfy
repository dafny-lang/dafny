// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var r0, r1;

  var d := Ctor(15);
  r0 := d.ToString();
  r1 := d.GetHashCode();
  print r0, " ", r1, "\n";

  var c := CoCtor(15);
  r0 := c.ToString();
  r1 := c.GetHashCode();
  print c.c, " ", c.d, " ", c.Computer(), " ";
  print r0, " ", r1, "\n";

  var n: NameclashNew := 3;
  r0 := n.ToString();
  r1 := n.GetHashCode();
  print r0, " ", r1, "\n";
}

datatype Nameclash = Ctor(x: int)
{
  method ToString() returns (o: real) { return 15.0; }
  method GetHashCode() returns (o: real) { return 15.1; }
}

codatatype NameclashCo = CoCtor(x: int)
{
  const c: int := 94
  const d: int := 99
  function Computer(): real { 0.8 }
  method Get() returns (u: int) { return 79; }
  method ToString() returns (o: real) { return 14.3; }
  method GetHashCode() returns (o: real) { return 14.4; }
}

newtype NameclashNew = x | -18 <= x < 20
{
  method ToString() returns (o: real) { return 18.9; }
  method GetHashCode() returns (o: real) { return 18.92; }
}
