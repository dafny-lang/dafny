// RUN: %baredafny run %args --target=cs "%s" %S/CSharpStyling2.cs > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var c := new MyClass(50);
  print c.u, "\n";  // 50
  c := new MyClass.Init(true);
  print c.u, "\n";  // 2
  c := new MyClass.Make(true);
  print c.u, "\n";  // 3

  var r, s;
  r := c.OneResultExtern(2);
  print r, "\n";  // 12
  r := c.OneResult(2);
  print r, "\n";  // 12
  r, s := c.TwoResultsExtern(0);
  print r, " ", s, "\n";  // 5 7
  r, s := c.TwoResults(0);
  print r, " ", s, "\n";  // 5 7
}

class MyClass {
  var u: int
  constructor {:extern} (x: int)
  constructor Init(y: bool) {
    u := if y then 2 else -2;
  }
  constructor {:extern} Make(y: bool)
  method {:extern} OneResultExtern(z: int) returns (r: int)
  method OneResult(z: int) returns (r: int) {
    r := 12;
    if z == 0 {
      r := 8;
      return r;
    } else if z == 1 {
      r := 10;
      return;
    }
  }
  method {:extern} TwoResultsExtern(z: int) returns (r: int, s: int)
  method TwoResults(z: int) returns (r: int, s: int) {
    if z == 0 {
      return 5, 7;
    } else {
      r, s := 9, 11;
    }
  }
}
