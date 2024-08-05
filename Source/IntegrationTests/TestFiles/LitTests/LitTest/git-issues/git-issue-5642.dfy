// RUN: %testDafnyForEachCompiler "%s"

class Cl {
  const c: bool
  constructor(c: bool) {
    this.c := c;
    this.c := c;
  }
}

method Main() {
  var cl := new Cl(false);
  print cl.c, "\n";
}