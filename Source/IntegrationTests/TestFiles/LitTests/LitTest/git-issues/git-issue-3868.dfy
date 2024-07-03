// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  var r := NotOptimized("let");
  print r, "\n"; // 15
  var recur := new Recur(25);
  print NotSoDeep("1900"), "\n";
  print WoahThat'sDeep(A, "42"), "\n";
  print WoahThat'sDeepToo(AA("i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x"), "555"), "\n";
  print "Recur: ", recur.Follow0(A, 12, 80), "\n"; // 116 (that is, 80 + 12*(2 + 1)
  print "Recur: ", recur.Follow1(A, 12, 80), "\n"; // 116 (that is, 80 + 12*(2 + 1)
  var w := DeepAssignment(25);
  print w, "\n"; // 25
  MatchExpressions.Test();
}

method NotOptimized(s: string) returns (r: int) {
  return (var abc := |s|; 3 * abc) + (var xyz := |s|; xyz + xyz);
}

function NotSoDeep(x: string): Option<string> {
  var x1 := x;
  var x2 := x1;
  var x3 := x2;
  var x4 := x3;
  var x5 := x4;
  var x6 := x5;
  var x7 := x6;
  var x8 := x7;
  var x9 := x8;
  var x10 := x9;
  Some(x10)
}

datatype Or = A | B

function WoahThat'sDeep(o: Or, x: string): Option<string> {
  var r :- match o {
    case A =>
      var x1 := x;
      var x2 := x1;
      var x3 := x2;
      var x4 := x3;
      var x5 := x4;
      var x6 := x5;
      var x7 := x6;
      var x8 := x7;
      var x9 := x8;
      var x10 := x9;
      Some(x10)
    case B =>
      Some("hello")
  };
  Some(r)
}

datatype AB = 
  | AA(x1: string, x2: string, x3: string, x4: string, x5: string, x6: string, x7: string, x8: string, x9: string, x10: string)
  | BB

function WoahThat'sDeepToo(ab: AB, x: string): Option<string> {
  var r :- match ab {
    case AA(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) =>
      Some(x10)
    case BB =>
      Some("hello")
  };
  Some(r)
}

class Recur {
  var next: Recur?
  var data: int

  constructor (n: nat) {
    data := 2;
    if n == 0 {
      next := null;
    } else {
      next := new Recur(n - 1);
    }
  }

  function Follow0(o: Or, n: nat, m: int): int
    reads *
  {
    var th := this;
    if n == 0 || next == null then
      m
    else
      var r := match o {
        case A =>
          // Note: The following mensions "_this", but instead the code uses "th". This
          // can be changed back to saying "_this" (and not using "th" at all) after the fix of
          // https://github.com/dafny-lang/dafny/issues/4684
          //
          // Because this call is tail recursive, the "this" on the next line
          // is compiled into a local variable "_this" and in-parameter "n" becomes
          // mutable in the target code. Since the whole body of this "match o" is
          // compiled into a lambda, that mutable "_this" and "n" variables cannot be
          // used (in some target languages). Instead, the compiler (via the "inLetExprBody"
          // parameter, see SinglePassCompiler.cs) arranges to make a copy of
          // "_this" and "n" into "effectively final" local variables.
          // By using "this" and "n" in the following line, we test that "inLetExprBody"
          // is passed around appropriately.
          var x1 := n + th.data - n; // 2
          var x2 := x1;
          var x3 := x2;
          var x4 := x3;
          var x5 := x4;
          var x6 := x5;
          var x7 := x6;
          var x8 := x7;
          var x9 := x8;
          var x10 := x9;
          x10
        case B =>
          999
      };
      next.Follow0(o, n - 1, m + r) + 1 // accumulator tail recursion
  }

  // This function has an auto-accumulator recursive call inside the match. However,
  // this entire compilation uses TrExprOpt, so the point about using things inside
  // lambda expressions in the target language do not come arise.
  function Follow1(o: Or, n: nat, m: int): int
    reads *
  {
    var th := this;
    if n == 0 || next == null then
      m
    else
      match o {
        case A =>
          var x1 := n + th.data - n; // 2
          var x2 := x1;
          var x3 := x2;
          var x4 := x3;
          var x5 := x4;
          var x6 := x5;
          var x7 := x6;
          var x8 := x7;
          var x9 := x8;
          var x10 := x9;
          next.Follow1(o, n - 1, m + th.data) + 1 // accumulator tail recursion
        case B =>
          999
      }
  }
}

datatype Option<+T> = None | Some(value: T) {
  predicate IsFailure() {
    None?
  }

  function PropagateFailure<U>(): Option<U>
    requires None?
  {
    None
  }

  function Extract(): T
    requires Some?
  {
    value
  }
}

method DeepAssignment(x: int) returns (r: int) {
  r :=
    var x0 := x;
    var x1 := x0;
    var x2 := x1;
    var x3 := x2;
    var x4 := x3;
    var x5 := x4;
    var x6 := x5;
    var x7 := x6;
    if x0 == x7 then
      var y0 := x;
      var y1 := y0;
      y1
    else
      var y2 := x;
      var y3 := y2;
      y3;
  return r;
}

module MatchExpressions {
  datatype Color = Red | Green | Blue
  datatype AB = A | B
  datatype ABC = AA | BB | CC

  method Test() {
    M(Green);
    N(Red);
    var r := O(Blue, 10);
    print r, "\n"; // 12
    P(7, 2);
    label L: {
      var abc := 0;
      break L;
    }
    print TailRecursive(A, 19), " ", AutoAccumulator(A, 19), "\n"; // 6 25
    print LastCaseIsDisjunctive(BB), "\n"; // 22
    print F(A, 12, 80), "\n"; // 80
    print "It's done\n";
  }

  method M(c: Color) {
    var x := match c
      case Red => 5
      case Green => 7
      case Blue => 11;
    print x, "\n"; // 5
  }

  method N(c: Color)
    requires c == Red
  {
    var x := match c
      case Red => 5;
    print x, "\n"; // 5
  }

  method O(c: Color, y: int) returns (r: int)
    requires 0 <= y
  {
    if y < 0 {
      // unreachable
      var x: int := match c;
    }
    r := 12;
  }

  method P(s: int, t: int)
    requires t == 0 || t == 2
  {
    var x: int := match s
      case 0 => 100
      case 2 => 200
      case _ => 400;
    var y: int := match t
      case 0 => 60
      case 2 => 80;
    if t == 1 {
      // unreachable
      var z: int := match s + t;
    }
    print x, " ", y, "\n"; // 400 80
  }

  function TailRecursive(o: AB, n: nat): int {
    if n == 0 then 6 else
      match o
      case A | B => TailRecursive(o, n - 1)
  }

  function AutoAccumulator(o: AB, n: nat): int {
    if n == 0 then 6 else
      match o
      case A | B => AutoAccumulator(o, n - 1) + 1
  }

  function LastCaseIsDisjunctive(o: ABC): int {
    match o
    case CC =>
      777
    case AA | BB =>
      22
  }

  function F(o: AB, n: nat, m: int): int
  {
    if n == 0 then
      m
    else if n == 1 then
      var ff := () => match o { // for Java, make sure o is copied
        case A => 20
        case B => 999
      };
      var s := ff();
      F(o, n - 1, m)
    else
      var u := match o {
        case A => 20
        case B => 999
      };
      F(o, n - 1, m)
  }
}
