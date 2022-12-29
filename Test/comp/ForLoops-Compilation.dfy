// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  TestM(0, 0);
  TestM(-2, 2);
  TestM(-2, 3);
  TestM(10, 20);

  TestP(0, 0);
  TestP(28, 28);
  TestP(28, 30);
  TestP(255, 255); // this one requires an unsigned comparison in Java
  TestP(0, 255);

  TestQ(-128, -128);
  TestQ(-128, -127);
  TestQ(126, 127);
  TestQ(127, 127);

  Mul(0, 2);
  Mul(2, 0);
  Mul(1, 1);
  Mul(6, 5);

  Add(0, 3);
  Add(3, 0);
  Add(4, 0);
  Add(0, 0);
  Add(19, 14);

  BreaksAndContinues();
}

method TestM(lo: int, hi: int)
  requires lo <= hi
{
  var s, t := M0(lo, hi);
  var u, v := M1(lo, hi);
  print s, " ", t, " ", u, " ", v, "\n";
}

method TestP(lo: byte, hi: byte)
  requires lo <= hi
{
  var s, t := P(lo, hi);
  print s, " ", t, "\n";
}

method TestQ(lo: i8, hi: i8)
  requires lo <= hi
{
  var s, t := Q(lo, hi);
  print s, " ", t, "\n";
}

method M0(lo: int, hi: int) returns (s: int, t: int)
  requires lo <= hi
{
  s, t := 0, 0;
  for i := lo to hi {
    s := s + i;
  }
  for i := hi downto lo {
    t := t + i;
  }
}

method M1(lo: int, hi: int) returns (s: int, t: int)
  requires lo <= hi
{
  s, t := 0, 0;
  for i := lo to *
    invariant i <= hi
    decreases hi - i
  {
    if i == hi {
      break;
    }
    s := s + i;
  }
  if lo < hi {
    for i := hi downto *
      invariant lo <= i
      decreases i - lo
    {
      if i == lo - 1 {
        break;
      }
      t := t + i;
    }
  }
}

newtype byte = x | 0 <= x < 256

method P(lo: byte, hi: byte) returns (s: int, t: int)
  requires lo <= hi
{
  s, t := 0, 0;
  for i := lo to hi {
    s := s + i as int;
  }
  for i := hi downto lo {
    t := t + i as int;
  }
}

newtype i8 = x | -128 <= x < 128

method Q(lo: i8, hi: i8) returns (s: int, t: int)
  requires lo <= hi
{
  s, t := 0, 0;
  for i := lo to hi {
    s := s + i as int;
  }
  for i := hi downto lo {
    t := t + i as int;
  }
}

method Mul(a: nat, b: nat) {
  var c := 0;
  var aa := a;
  for _ := 0 to aa {
    var bb := b;
    for _ := bb downto 0 {
      c, bb, aa := c + 1, bb + 3, aa + 2;
    }
    aa := aa + 5;
  }
  print a, " * ", b, " == ", c, "\n";
}

method Add(a: nat, b: nat) {
  var s := 0;
  label Outer0:
  label Outer1:
  for _ := 0 to 7 {
    for i := 0 to *
      invariant i <= a
      decreases a - i
    {
      if i == a {
        if i % 2 == 0 {
          break Outer0;
        } else {
          break Outer1;
        }
      }
      if a < i {
        break; // never reached
      }
      s := s + 1;
    }
    s := 77; // never reached
  }
  for _ := 2 to 3 {
    label Inner:
    for i: int := b downto *
      invariant 0 <= i
      decreases i
    {
      if i < 0 {
        break Inner;
      }
      s := s + 1;
    }
  }
  print a, " + ", b, " == ", s, "\n";
}

// --------------- breaks and continues ---------------

method BreaksAndContinues() {
  var n0 := BC0();
  var n1 := BC1();
  var n2 := BC2();
  print n0, " ", n1, " ", n2, "\n"; // 4 4 4

  BC10();
  BC11();

  var b0 := BC20();
  var b1 := BC21();
  var b2 := BC22();
  var c := BC30();
  print b0, " ", b1, " ", b2, " ", c, "\n"; // true true true 15

  LabelRegressions();
}

method BC0() returns (c: nat) { // 4
  c := 0;
  var i := 0;
  while i < 10 { // 0 3 4 7
    c := c + 1;
    if i % 2 == 0 {
      i := i + 3;
      continue;
    } else if i == 7 {
      break;
    }
    i := i + 1;
  }
}

method BC1() returns (c: nat) { // 4
  c := 0;
  var i := 0;
  while // 0 3 4 7
    decreases 10 - i
  case i < 10 && i % 2 == 0 =>
    c := c + 1;
    i := i + 3;
    continue;
  case i < 10 && i == 7 =>
    c := c + 1;
    break;
  case i < 10 && i != 7 && i % 2 == 1 =>
    c := c + 1;
    i := i + 1;
}

method BC2() returns (c: nat) { // 4
  c := 0;
  var i := 0;
  for k := 0 to 10 { // 0 3 4 7
    c := c + 1;
    if i % 2 == 0 {
      i := i + 3;
      continue;
    } else if i == 7 {
      expect k == 3;
      break;
    }
    i := i + 1;
  }
}

// Test "break", "continue", and "break continue" for "for" loops
method BC10() {
  print "== BC10 ==";
  for i := 0 to 10 {
    print "\n", i, " ";
    for j := 0 to 10 {
      print "--";
      if i == 0 && j == 3 {
        break;
      } else if i == 1 && j == 4 {
        break continue;
      } else if j == 2 {
        continue;
      }
      print "++";
    }
    print " ***";
  }
  print "\n";
}

// Test "break", "continue", and "break continue" for "while" and "while-case" loops
method BC11() {
  print "== BC11 ==";
  var i := 0;
  while i < 10
  {
    print "\n", i, " ";
    i := i + 1;
    var j := 0;
    var b := true;
    while
      decreases 10 - j, b
    {
      case j < 10 && !b =>
        print "--";
        if i - 1 == 0 && j == 3 {
          break;
        } else if i - 1 == 1 && j == 4 {
          break continue;
        } else if j == 1 {
          j := j + 1;
          continue;
        }
        print "++";
        j := j + 1;
      case j < 10 && b =>
        print "||";
        b := false;
    }
    print " ***";
  }
  print "\n";
}

// Test "continue Label" and "break Label" for "while" loops
method BC20() returns (b: bool) {
  b := false;
  var i := 0;
  label Loop:
  while i < 10 {
    if i == 929 {
    } else if i < 7 {
      i := i + 1;
      continue Loop;
    } else {
      b := true;
      break Loop;
    }
    assert false; // unreachable
    expect false; // unreachable
  }
}

// Test "continue Label" and "break Label" for "while-case" loops
method BC21() returns (b: bool) {
  b := false;
  var i := 0;
  label Loop:
  while
    decreases 10 - i
  {
    case i < 10 =>
      if i == 929 {
      } else if i < 7 {
        i := i + 1;
        continue Loop;
      } else {
        b := true;
        break Loop;
      }
      assert false; // unreachable
      expect false; // unreachable
  }
}

// Test "continue Label" and "break Label" for "for" loops
method BC22() returns (b: bool) {
  b := false;
  label Loop:
  for i := 0 to 10 {
    if i == 929 {
    } else if i < 7 {
      continue Loop;
    } else {
      b := true;
      break Loop;
    }
    assert false; // unreachable
    expect false; // unreachable
  }
}

// Test "break break"
method BC30() returns (c: nat) { // 15
  c := 0;
  while true {
    for k := 0 to 10
      invariant k <= 5
    {
      if k == 5 {
        break break;
      }
      c := c + 1;
    }
  }

  while {
    case true =>
      for k := 0 to 10
        invariant k <= 5
      {
        if k == 5 {
          break break;
        }
        c := c + 1;
      }
  }

  for i := 0 to 100 {
    for k := 0 to 10 {
      if k == 5 {
        break break;
      }
      c := c + 1;
    }
  }
}

method LabelRegressions() {
  // The cases of if-case, while-case, and match statements are List<Statement>'s, which are essentially
  // a BlockStmt but without the curly braces. Each Statement in such a List can have labels, so
  // it's important to call TrStmtList on these in the Verifier, not just call TrStmt on every Statement
  // in the List. (See also LabelRegressions() in Test/dafny0/ResolutionErrors.dfy.)
  if {
    case true =>
      label Loop:
      for k := 0 to 10 {
        if k % 2 == 0 {
          continue Loop;
        } else {
          break Loop;
        }
      }
  }

  while {
    case true =>
      label Loop:
      for k := 0 to 10 {
        if k % 2 == 0 {
          continue Loop;
        } else {
          break Loop;
        }
      }
      break;
  }

  match (0, 0) {
    case (_, _) =>
      label Loop:
      for k := 0 to 10 {
        if k % 2 == 0 {
          continue Loop;
        } else {
          break Loop;
        }
      }
  }

  print "all good\n";
}
