// RUN: %baredafny translate rs %args "%s"
// RUN: %OutputCheck --file-to-check "%S/datatypes-rust/src/datatypes.rs" "%s"
// CHECK: Gather\(self: &.*Rc<Self>
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Simple = SimpleConstructor()

datatype Multiple =
  | Constructor1(a: int)
  | Constructor2(b: bool)
  | Constructor3(a: int, b: bool)
{
  function Gather(other: Multiple): Multiple {
    if Constructor3? then this
    else if Constructor1? then
      if other.Constructor2? then
        Constructor3(a, other.b)
      else
        this
    else if Constructor2? then
      if other.Constructor1? then
        Constructor3(other.a, b)
      else
        this
    else
      this
  }
}

method Main() {
  var c := Constructor1(0);
  c := c.Gather(Constructor1(1));
  print c.Constructor1?, "\n";
  print c.a, "\n";
  c := c.Gather(Constructor2(true));
  print c.Constructor3?, "\n";
  print c.a, "\n";
  print c.b, "\n";
}