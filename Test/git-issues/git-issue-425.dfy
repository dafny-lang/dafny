method M() returns (x: int, ghost y: int)

datatype Color = Red | Blue
  
method Main() {
  var x0, y0 := M();  // this is fine: x0 is compiled, y0 is ghost
  var c: Color;
  match c
  case Red =>
    var x1, y1 := M();  // this used to generate an error, saying y1 is not ghost :(
  case Blue =>
}
