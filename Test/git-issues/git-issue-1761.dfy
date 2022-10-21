// RUN: %baredafny run %args "%s" --input %S/git-issue-1761-extern.cs > "%t"
// RUN: %diff "%s.expect" "%t"

class {:extern "ABC"} XYZ {
  var y: bool
  constructor {:extern} (x: bool) {
    y := x;
  }
}

method Main() {
  var xyz := new XYZ(true);
  print xyz.y, "\n";
}