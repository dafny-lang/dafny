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
