// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
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
