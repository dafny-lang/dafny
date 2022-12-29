// RUN: %baredafny run %args "%s" %S/git-issue-1761-extern.cs > "%t"
// RUN: %diff "%s.expect" "%t"

class {:extern "ABC"} XYZ {
  var y: bool
  constructor {:extern} Init(x: bool) {
    y := x;
  }
  constructor {:extern} Create(x: bool, z: bool) {
    y := x && z;
  }
}

method Main() {
  var xyz := new XYZ.Init(true);
  print xyz.y, "\n";
  xyz := new XYZ.Create(true, false);
  print xyz.y, "\n";
}
