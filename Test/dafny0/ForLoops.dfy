// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M0() {
  var limit, j := 100, 0;
  for i := 0 to limit
    invariant i == j
  {
    limit, j := limit + 1, j + 1;
  }
  assert j == 100;
}

method M1(lo: int, hi: int)
  requires lo <= hi
{
  for i := lo to hi {
    assert lo <= i < hi;
    assert i != 7; // error
  }
}

method M2(lo: int, hi: int) {
  for i := lo to hi { // error: lo may exceed hi
  }
}

newtype Nat = x | 0 <= x

method M3(n: Nat) returns (r: Nat)
  ensures r == n * n
{
  r := 0;
  for i := 0 to n
    invariant r == i * i
  {
    r := r + i + i + 1;
  }
}

method SumsUpAndDown(N: int)
  requires 0 <= N
{
  var s := 0;
  for i := N downto 0
    invariant s == N * (N - 1) / 2 - i * (i - 1) / 2
  {
    s := s + i;
  }
  for i := 0 to N
    invariant s == N * (N - 1) / 2 - i * (i - 1) / 2
  {
    s := s - i;
  }
  assert s == 0;
}

method Break0(n: nat) {
  var j := 0;
  for i := 0 to n
    invariant i == j <= n / 2
  {
    if i == n / 2 {
      break;
    }
    j := j + 1;
  }
  assert j == n / 2;
}

method Break1(n: nat) {
  var j := 0;
  label Outer:
  for i := 0 to n
    invariant i == j <= n / 2
  {
    for k := -1 to i
      invariant k < 0 || i < n / 2
    {
      if i == n / 2 {
        break Outer;
      }
    }
    j := j + 1;
  }
  assert j == n / 2;
}

method Break2(n: nat) {
  var j := 0;
  label Outer:
  for i := 0 to n
    invariant i == j
  {
    for k := -1 to i {
      if i == n / 2 {
        break;
      }
    }
    j := j + 1;
  }
  assert j == n;
}

method Break3(n: nat) {
  var j := 0;
  label OuterBlock: {
    for i := 0 to n
      invariant i == j <= n / 2
    {
      if i == n / 2 {
        break OuterBlock;
      }
      j := j + 1;
    }
    assert false; // error: n may be 0
  }
  assert j == n / 2;
}

method Break4(n: nat) {
  var j := 0;
  label OuterBlock: {
    for i := 0 to n
      invariant i == j <= n / 2
    {
      if i == n / 2 {
        break OuterBlock;
      }
      j := j + 1;
    }
    assert n == 0;
  }
  assert j == n / 2;
}

method Down0(n: nat) {
  var j := n;
  for i := n downto 0
    invariant i == j
  {
    j := j - 1;
    var x := 100 / (n - i);
  }
  assert j == 0;
}

method Down1(n: nat) {
  for i := n downto 0 {
    var x := 100 / i; // error: division by zero
  }
}

method Down2(lo: int, hi: int) {
  for i := hi downto lo { // error: lo may exceed hi
  }
}

method Down3(lo: int, hi: int)
  requires lo <= hi
{
  var Hi, Lo := 2 * hi, 2 * lo;
  var j := 2 * hi;
  for i := Hi downto Lo
    invariant i == j
  {
    j := j - 1;
    Hi, Lo := Hi - 1, Lo + 5;
  }
  assert j == 2 * lo;
}

method NoBoundUp(k: int)
  decreases *
  ensures 0 <= k
{
  for i := 0 to * {
    if i == k {
      return;
    }
  }
  assert false;
}

method NoBoundDown(k: int)
  decreases *
  ensures k < 0
{
  for i := 0 downto * {
    assert i != 0;
    if i == k {
      return;
    }
  }
  assert false;
}

type Even = x | x % 2 == 0
type NineToFive = x | 9 <= x < 17 witness 9

method SubsetType0(k: int)
  requires 0 <= k
{
  for i: Even := 0 to 2 * k { // error: not all values in the range [0..2*k] are Even
  }
}

method SubsetType1(k: int)
  requires k == 0
{
  for i: Even := 0 to 2 * k {
  }
}

method SubsetType2(lo: int, hi: int)
  requires lo <= hi
{
  for i: NineToFive := lo to hi { // error: not all values in [lo..hi] are NineToFive
  }
}

method SubsetType3(lo: int, hi: int)
  requires lo <= hi
{
  for i: NineToFive := hi downto lo { // error: not all values in [lo..hi] are NineToFive
  }
}

method SubsetType4(x: int) {
  for i: NineToFive := x to x { // error: x may not be a NineToFive
  }
}

method SubsetType5(lo: int, hi: int)
  requires lo <= hi
{
  if * {
    for i: NineToFive := 9 to 17 { // error: 17 is not NineToFive
    }
  } else {
    for i: NineToFive := 17 downto 9 { // error: 17 is not NineToFive
    }
  }
}

method SubsetType6(lo: int, hi: int)
  requires lo <= hi
{
  if * {
    var n := 0;
    for i: NineToFive := 9 to 16
      invariant n == i - 9
    {
      n := n + 1;
    }
    assert n == 7;
  } else {
    var n := 0;
    for i: NineToFive := 16 downto 9
      invariant n == 16 - i
    {
      n := n + 1;
    }
    assert n == 7;
  }
}

method SubsetType7(lo: int, hi: int)
  requires lo <= hi
{
  if * {
    for i: nat := lo to hi { // error: lo may not be a nat
    }
  } else {
    for i: nat := hi downto lo { // error: hi may not be a nat
    }
  }
}

type NotSeven = x | x != 7

method SubsetType8(start: int)
  requires start == 0 || start == 100
  decreases *
{
  if * {
    for i: NotSeven := start to * { // error: range may include 7
    }
  } else {
    for i: NotSeven := start downto * { // error: range may include 7
    }
  }
}

newtype byte = x | 0 <= x < 256

method Newtype0() {
  for i: byte := 0 to 256 // error: 256 is not a byte
    invariant i <= 10 // this doesn't matter for the range check on the previous line
  {
    if i == 3 { break; }
  }
}

method Newtype1() {
  for i: byte := 256 downto 0 { // error: 256 is not a byte
  }
}

method Newtype2() {
  for i := 0 to 256 { // error: 256 is not a byte (type inference infers i to be of type byte)
    var b: byte := i;
  }
}

method Newtype3() {
  for i := 0 to 256 {
    var b := i as byte;
  }
}

method Newtype4(lo: byte, hi: byte)
  requires lo <= hi
{
  for i := lo to hi {
  }
}

method BodylessFor0(lo: int, hi: int)
  requires lo <= hi
{
  var j := lo;
  for i := lo to hi // information: body-less loop (loop frame: i, j)
    invariant i == j
  assert j == hi;
}

method BodylessFor1(lo: int, hi: int)
  requires lo <= hi
{
  var j := lo;
  for i := lo to hi // information: body-less loop (loop frame: i, j)
    invariant i == j
  assert j < hi; // error
}

method BodylessFor2(lo: int, hi: int)
  requires lo <= hi
{
  var j := hi;
  for i := hi downto lo // information: body-less loop (loop frame: i, j)
    invariant i == j
  assert j == lo;
}

method BodylessFor3(lo: int, hi: int)
  requires lo <= hi
{
  var j := hi;
  for i := hi downto lo // information: body-less loop (loop frame: i, j)
    invariant i == j
  assert j == hi; // error
}

method BodylessFor4(lo: int, hi: int)
  requires lo <= hi
{
  var x, y := 6, 7;
  for i := lo to hi // information: body-less loop (loop frame: i, x)
    invariant x <= i || i < x
  assert y == 7;
  assert x == 6; // error
}

method NonTermination0(start: int, up: bool)
  decreases *
{
  if up {
    for i := start to * {
    }
  } else {
    for i := start downto * {
    }
  }
}

method NonTermination1(start: int, up: bool)
  decreases *
{
  if up {
    for i := start to *
      decreases *
    {
    }
  } else {
    for i := start downto *
      decreases *
    {
    }
  }
}

method Termination(start: int, up: bool) {
  if up {
    for i := start to *
      invariant i <= start + 768
      decreases start + 1000 - i
    {
      if i == start + 768 {
        break;
      }
    }
  } else if * {
    for i := start downto *
      invariant start - 768 <= i // error: invariant not maintained
      decreases i - start + 1000
    {
      if i == start - 768 {
        return;
      }
    }
  } else if * {
    for i := start downto *
      invariant start - 768 < i
      decreases i - start + 766
    {
      if i == start - 768 {
        return;
      }
    }
  } else if * {
    for i := start downto *
      invariant start - 768 < i
      decreases i - start + 765 // error: not bounded below
    {
      if i == start - 768 {
        return;
      }
    }
  } else {
    for i := start downto *
      invariant start - 768 < i
      decreases i + 1000 // error: not bounded below
    {
      if i == start - 768 {
        return;
      }
    }
  }
}

method Underscores() {
  for _ := 0 to 10 {
    for _ := 2 to 8 {
    }
  }
  assert false; // error
}
