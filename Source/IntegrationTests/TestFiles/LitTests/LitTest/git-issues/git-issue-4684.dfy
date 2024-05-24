// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

class C {
  var data: nat
  var next: C?

  constructor (n: nat) {
    data := n;
    if n == 0 {
      next := null;
    } else {
      next := new C(n - 1);
    }
  }

  function FWithoutTailRecursion(n: nat, g: () ~> int): int
    requires g.requires()
    reads *
  {
    if n == 0 || next == null then
      g()
    else
      var h := () reads this => this.data;
      var r := next.FWithoutTailRecursion(n - 1, if n < 20 then g else h);
      r
  }

  function F(n: nat, g: () ~> int): int
    requires g.requires()
    reads *
  {
    if n == 0 || next == null then
      g()
    else
      var h := () reads this => this.data;
      next.F(n - 1, if n < 20 then g else h)
  }
}

method Main() {
  var c := new C(25);
  print c.FWithoutTailRecursion(25, () => -1), "\n"; // 20
  print c.F(25, () => -1), "\n"; // 20
}
