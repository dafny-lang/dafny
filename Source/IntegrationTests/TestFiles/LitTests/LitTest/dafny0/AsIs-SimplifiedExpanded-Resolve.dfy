// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method IsBasicTypes(a0: bool, a1: char, a2: int, a3: bv7, a4: bv13, a5: ORDINAL, a6: real)
{
  if
  case true =>
    var _ := a0 is bool;
    var _ := a0 is char; // error
    var _ := a0 is int; // error
    var _ := a0 is bv7; // error
    var _ := a0 is bv13; // error
    var _ := a0 is ORDINAL; // error
    var _ := a0 is real; // error
  case true =>
    var _ := a1 is bool; // error
    var _ := a1 is char;
    var _ := a1 is int;
    var _ := a1 is bv7; // error
    var _ := a1 is bv13; // error
    var _ := a1 is ORDINAL; // error
    var _ := a1 is real; // error
  case true =>
    var _ := a2 is bool; // error
    var _ := a2 is char;
    var _ := a2 is int;
    var _ := a2 is bv7;
    var _ := a2 is bv13;
    var _ := a2 is ORDINAL;
    var _ := a2 is real;
  case true =>
    var _ := a3 is bool; // error
    var _ := a3 is char; // error
    var _ := a3 is int;
    var _ := a3 is bv7;
    var _ := a3 is bv13;
    var _ := a3 is ORDINAL; // error
    var _ := a3 is real; // error
  case true =>
    var _ := a4 is bool; // error
    var _ := a4 is char; // error
    var _ := a4 is int;
    var _ := a4 is bv7;
    var _ := a4 is bv13;
    var _ := a4 is ORDINAL; // error
    var _ := a4 is real; // error
  case true =>
    var _ := a5 is bool; // error
    var _ := a5 is char; // error
    var _ := a5 is int;
    var _ := a5 is bv7; // error
    var _ := a5 is bv13; // error
    var _ := a5 is ORDINAL;
    var _ := a5 is real; // error
  case true =>
    var _ := a6 is bool; // error
    var _ := a6 is char; // error
    var _ := a6 is int;
    var _ := a6 is bv7; // error
    var _ := a6 is bv13; // error
    var _ := a6 is ORDINAL; // error
    var _ := a6 is real;
}

method AsBasicTypes(a0: bool, a1: char, a2: int, a3: bv7, a4: bv13, a5: ORDINAL, a6: real)
{
  if
  case true =>
    var _ := a0 as bool;
    var _ := a0 as char; // error
    var _ := a0 as int; // error
    var _ := a0 as bv7; // error
    var _ := a0 as bv13; // error
    var _ := a0 as ORDINAL; // error
    var _ := a0 as real; // error
  case true =>
    var _ := a1 as bool; // error
    var _ := a1 as char;
    var _ := a1 as int;
    var _ := a1 as bv7; // error
    var _ := a1 as bv13; // error
    var _ := a1 as ORDINAL; // error
    var _ := a1 as real; // error
  case true =>
    var _ := a2 as bool; // error
    var _ := a2 as char;
    var _ := a2 as int;
    var _ := a2 as bv7;
    var _ := a2 as bv13;
    var _ := a2 as ORDINAL;
    var _ := a2 as real;
  case true =>
    var _ := a3 as bool; // error
    var _ := a3 as char; // error
    var _ := a3 as int;
    var _ := a3 as bv7;
    var _ := a3 as bv13;
    var _ := a3 as ORDINAL; // error
    var _ := a3 as real; // error
  case true =>
    var _ := a4 as bool; // error
    var _ := a4 as char; // error
    var _ := a4 as int;
    var _ := a4 as bv7;
    var _ := a4 as bv13;
    var _ := a4 as ORDINAL; // error
    var _ := a4 as real; // error
  case true =>
    var _ := a5 as bool; // error
    var _ := a5 as char; // error
    var _ := a5 as int;
    var _ := a5 as bv7; // error
    var _ := a5 as bv13; // error
    var _ := a5 as ORDINAL;
    var _ := a5 as real; // error
  case true =>
    var _ := a6 as bool; // error
    var _ := a6 as char; // error
    var _ := a6 as int;
    var _ := a6 as bv7; // error
    var _ := a6 as bv13; // error
    var _ := a6 as ORDINAL; // error
    var _ := a6 as real;
}

// SOON: newtype NT<Y> = pair: (Y, int) | 0 <= pair.1 < 8 witness *

type AbstractType<+X, Y, -Z>

trait INT { }
class NAT extends INT { }

method IsParameterOrAbstract<T, U>(a: AbstractType<INT, INT, INT>, b: AbstractType<NAT, NAT, NAT>, t: T)
{
  if
  case true =>
    var _ := a is T; // error
    var _ := a is U; // error
    var _ := a is int; // error
    var _ := a is nat; // error
    var _ := a is AbstractType<NAT, NAT, NAT>; // error
    var _ := a is AbstractType<NAT, NAT, INT>; // error
    var _ := a is AbstractType<NAT, INT, NAT>; // error
    var _ := a is AbstractType<NAT, INT, INT>;
    var _ := a is AbstractType<INT, NAT, NAT>; // error
    var _ := a is AbstractType<INT, NAT, INT>; // error
    var _ := a is AbstractType<INT, INT, NAT>;
    var _ := a is AbstractType<INT, INT, INT>;
    var _ := a is (int, int); // error
    var _ := a is set<int>; // error
    var _ := a is object; // error
    var _ := a is array2<int>; // error
    // SOON: var _ := a is NT<int>; // error
  case true =>
    var _ := b is T; // error
    var _ := b is U; // error
    var _ := b is int; // error
    var _ := b is nat; // error
    var _ := b is AbstractType<NAT, NAT, NAT>;
    var _ := b is AbstractType<NAT, NAT, INT>;
    var _ := b is AbstractType<NAT, INT, NAT>; // error
    var _ := b is AbstractType<NAT, INT, INT>; // error
    var _ := b is AbstractType<INT, NAT, NAT>;
    var _ := b is AbstractType<INT, NAT, INT>; // error
    var _ := b is AbstractType<INT, INT, NAT>; // error
    var _ := b is AbstractType<INT, INT, INT>; // error
    var _ := b is (int, int); // error
    var _ := b is set<int>; // error
    var _ := b is object; // error
    var _ := b is array2<int>; // error
    // SOON: var _ := b is NT<int>; // error
  case true =>
    var _ := t is T;
    var _ := t is U; // error
    var _ := t is int; // error
    var _ := t is nat; // error
    var _ := t is AbstractType<NAT, NAT, NAT>; // error
    var _ := t is AbstractType<NAT, NAT, INT>; // error
    var _ := t is AbstractType<NAT, INT, NAT>; // error
    var _ := t is AbstractType<NAT, INT, INT>; // error
    var _ := t is AbstractType<INT, NAT, NAT>; // error
    var _ := t is AbstractType<INT, NAT, INT>; // error
    var _ := t is AbstractType<INT, INT, NAT>; // error
    var _ := t is AbstractType<INT, INT, INT>; // error
    var _ := t is (int, int); // error
    var _ := t is set<int>; // error
    var _ := t is object; // error
    var _ := t is array2<int>; // error
    // SOON: var _ := t is NT<int>; // error
}

method AsParameterOrAbstract<T, U>(a: AbstractType<INT, INT, INT>, b: AbstractType<NAT, NAT, NAT>, t: T)
{
  if
  case true =>
    var _ := a as T; // error
    var _ := a as U; // error
    var _ := a as int; // error
    var _ := a as nat; // error
    var _ := a as AbstractType<NAT, NAT, NAT>; // error
    var _ := a as AbstractType<NAT, NAT, INT>; // error
    var _ := a as AbstractType<NAT, INT, NAT>; // error
    var _ := a as AbstractType<NAT, INT, INT>;
    var _ := a as AbstractType<INT, NAT, NAT>; // error
    var _ := a as AbstractType<INT, NAT, INT>; // error
    var _ := a as AbstractType<INT, INT, NAT>;
    var _ := a as AbstractType<INT, INT, INT>;
    var _ := a as (int, int); // error
    var _ := a as set<int>; // error
    var _ := a as object; // error
    var _ := a as array2<int>; // error
    // SOON: var _ := a as NT<int>; // error
  case true =>
    var _ := b as T; // error
    var _ := b as U; // error
    var _ := b as int; // error
    var _ := b as nat; // error
    var _ := b as AbstractType<NAT, NAT, NAT>;
    var _ := b as AbstractType<NAT, NAT, INT>;
    var _ := b as AbstractType<NAT, INT, NAT>; // error
    var _ := b as AbstractType<NAT, INT, INT>; // error
    var _ := b as AbstractType<INT, NAT, NAT>;
    var _ := b as AbstractType<INT, NAT, INT>; // error
    var _ := b as AbstractType<INT, INT, NAT>; // error
    var _ := b as AbstractType<INT, INT, INT>; // error
    var _ := b as (int, int); // error
    var _ := b as set<int>; // error
    var _ := b as object; // error
    var _ := b as array2<int>; // error
    // SOON: var _ := b as NT<int>; // error
  case true =>
    var _ := t as T;
    var _ := t as U; // error
    var _ := t as int; // error
    var _ := t as nat; // error
    var _ := t as AbstractType<NAT, NAT, NAT>; // error
    var _ := t as AbstractType<NAT, NAT, INT>; // error
    var _ := t as AbstractType<NAT, INT, NAT>; // error
    var _ := t as AbstractType<NAT, INT, INT>; // error
    var _ := t as AbstractType<INT, NAT, NAT>; // error
    var _ := t as AbstractType<INT, NAT, INT>; // error
    var _ := t as AbstractType<INT, INT, NAT>; // error
    var _ := t as AbstractType<INT, INT, INT>; // error
    var _ := t as (int, int); // error
    var _ := t as set<int>; // error
    var _ := t as object; // error
    var _ := t as array2<int>; // error
    // SOON: var _ := t as NT<int>; // error
}

method IsCollectionUserDefined(a: set<int>, b: (int, int), c: array2<int>)
{
  if
  case true =>
    var _ := a is int; // error
    var _ := a is set<int>;
    var _ := a is (int, int); // error
    var _ := a is array2<int>; // error
    // SOON: var _ := a is NT<real, int>; // error
    // SOON: var _ := a is NT<int, int>; // error
  case true =>
    var _ := b is int; // error
    var _ := b is set<int>; // error
    var _ := b is (int, int);
    var _ := b is array2<int>; // error
    // SOON: var _ := b is NT<real, int>; // error
    // SOON: var _ := b is NT<int, int>;
  case true =>
    var _ := c is int; // error
    var _ := c is set<int>; // error
    var _ := c is (int, int); // error
    var _ := c is array2<int>;
    // SOON: var _ := c is NT<real, int>; // error
    // SOON: var _ := c is NT<int, int>; // error
}

method AsCollectionUserDefined(a: set<int>, b: (int, int), c: array2<int>)
{
  if
  case true =>
    var _ := a as int; // error
    var _ := a as set<int>;
    var _ := a as (int, int); // error
    var _ := a as array2<int>; // error
    // SOON: var _ := a as NT<real, int>; // error
    // SOON: var _ := a as NT<int, int>; // error
  case true =>
    var _ := b as int; // error
    var _ := b as set<int>; // error
    var _ := b as (int, int);
    var _ := b as array2<int>; // error
    // SOON: var _ := b as NT<real, int>; // error
    // SOON: var _ := b as NT<int, int>;
  case true =>
    var _ := c as int; // error
    var _ := c as set<int>; // error
    var _ := c as (int, int); // error
    var _ := c as array2<int>;
    // SOON: var _ := c as NT<real, int>; // error
    // SOON: var _ := c as NT<int, int>; // error
}

newtype NewInt = int
newtype NewNewInt = NewInt

// SOON: newtype NewDiagonal<X> = diagonal: (X, X) | true witness *
// SOON: newtype NewNewDiagonal<X> = diagonal: NewDiagonal<X> | true witness *

method IsNewtype(a: int, b: NewInt, c: NewNewInt /** SOON, x: (int, int), y: NewDiagonal<int>, z: NewNewDiagonal<int> **/)
{
  if
  case true =>
    var _ := a is bool; // error
    var _ := a is char;
    var _ := a is int;
    var _ := a is NewInt;
    var _ := a is NewNewInt;
    // SOON: var _ := a is NewDiagonal<int>; // error
  case true =>
    var _ := b is bool; // error
    var _ := b is char;
    var _ := b is int;
    var _ := b is NewInt;
    var _ := b is NewNewInt;
    // SOON: var _ := b is NewDiagonal<int>; // error
  case true =>
    var _ := c is bool; // error
    var _ := c is char;
    var _ := c is int;
    var _ := c is NewInt;
    var _ := c is NewNewInt;
    // SOON: var _ := c is NewDiagonal<int>;
  /** SOON
  case true =>
    var _ := x is int; // error
    var _ := x is (int, int);
    var _ := x is NewDiagonal<int>;
    var _ := x is NewNewDiagonal<int>; // error
    var _ := x is NewDiagonal<nat>; // error
  case true =>
    var _ := y is int; // error
    var _ := y is (int, int);
    var _ := y is NewDiagonal<int>;
    var _ := y is NewNewDiagonal<int>;
    var _ := y is NewDiagonal<nat>; // error
  case true =>
    var _ := z is int; // error
    var _ := z is (int, int); // error
    var _ := z is NewDiagonal<int>;
    var _ := z is NewNewDiagonal<int>;
    var _ := z is NewDiagonal<nat>; // error
  **/
}

method AsNewtype(a: int, b: NewInt, c: NewNewInt /** SOON, x: (int, int), y: NewDiagonal<int>, z: NewNewDiagonal<int> **/)
{
  if
  case true =>
    var _ := a as bool; // error
    var _ := a as char;
    var _ := a as int;
    var _ := a as NewInt;
    var _ := a as NewNewInt;
    // SOON: var _ := a as NewDiagonal<int>; // error
  case true =>
    var _ := b as bool; // error
    var _ := b as char;
    var _ := b as int;
    var _ := b as NewInt;
    var _ := b as NewNewInt;
    // SOON: var _ := b as NewDiagonal<int>; // error
  case true =>
    var _ := c as bool; // error
    var _ := c as char;
    var _ := c as int;
    var _ := c as NewInt;
    var _ := c as NewNewInt;
    // SOON: var _ := c as NewDiagonal<int>;
  /** SOON
  case true =>
    var _ := x as int; // error
    var _ := x as (int, int);
    var _ := x as NewDiagonal<int>;
    var _ := x as NewNewDiagonal<int>; // error
    var _ := x as NewDiagonal<nat>; // error
  case true =>
    var _ := y as int; // error
    var _ := y as (int, int);
    var _ := y as NewDiagonal<int>;
    var _ := y as NewNewDiagonal<int>;
    var _ := y as NewDiagonal<nat>; // error
  case true =>
    var _ := z as int; // error
    var _ := z as (int, int); // error
    var _ := z as NewDiagonal<int>;
    var _ := z as NewNewDiagonal<int>;
    var _ := z as NewDiagonal<nat>; // error
  **/
}

trait AAA { }
trait BBB extends AAA { }

trait CCC extends BBB { }
datatype DDD extends BBB = DDD
class EEE extends BBB { }

method IsTrait(a: AAA, b: BBB, c: CCC, d: DDD, e: EEE)
{
  if
  case true =>
    var _ := a is AAA;
    var _ := a is BBB;
    var _ := a is CCC;
    var _ := a is DDD;
    var _ := a is EEE;
  case true =>
    var _ := b is AAA;
    var _ := b is BBB;
    var _ := b is CCC;
    var _ := b is DDD;
    var _ := b is EEE;
  case true =>
    var _ := c is AAA;
    var _ := c is BBB;
    var _ := c is CCC;
    var _ := c is DDD; // error
    var _ := c is EEE; // error
  case true =>
    var _ := d is AAA;
    var _ := d is BBB;
    var _ := d is CCC; // error
    var _ := d is DDD;
    var _ := d is EEE; // error
  case true =>
    var _ := e is AAA;
    var _ := e is BBB;
    var _ := e is CCC; // error
    var _ := e is DDD; // error
    var _ := e is EEE;
}

method AsTrait(a: AAA, b: BBB, c: CCC, d: DDD, e: EEE)
{
  if
  case true =>
    var _ := a as AAA;
    var _ := a as BBB;
    var _ := a as CCC;
    var _ := a as DDD;
    var _ := a as EEE;
  case true =>
    var _ := b as AAA;
    var _ := b as BBB;
    var _ := b as CCC;
    var _ := b as DDD;
    var _ := b as EEE;
  case true =>
    var _ := c as AAA;
    var _ := c as BBB;
    var _ := c as CCC;
    var _ := c as DDD; // error
    var _ := c as EEE; // error
  case true =>
    var _ := d as AAA;
    var _ := d as BBB;
    var _ := d as CCC; // error
    var _ := d as DDD;
    var _ := d as EEE; // error
  case true =>
    var _ := e as AAA;
    var _ := e as BBB;
    var _ := e as CCC; // error
    var _ := e as DDD; // error
    var _ := e as EEE;
}

type Triple<X> = (X, X, X)
type TA<X> = t: Triple<X> | P(t.0) witness *
type TB<X> = t: Triple<X> | P(t.1) witness *
type TBB<X> = t: TB<X> | P(t.2) witness *
predicate P<X>(x: X)

method IsSubsetType<Y>(t0: (Y, Y, Y), t1: Triple<Y>, ta: TA<Y>, tb: TB<Y>, tbb: TBB<Y>)
{
  if
  case true =>
    var _ := t0 is (int, int, int); // error
    var _ := t0 is (Y, Y, Y);
    var _ := t0 is Triple<Y>;
    var _ := t0 is TA<Y>;
    var _ := t0 is TB<Y>;
    var _ := t0 is TBB<Y>;
  case true =>
    var _ := t1 is (int, int, int); // error
    var _ := t1 is (Y, Y, Y);
    var _ := t1 is Triple<Y>;
    var _ := t1 is TA<Y>;
    var _ := t1 is TB<Y>;
    var _ := t1 is TBB<Y>;
  case true =>
    var _ := ta is (int, int, int); // error
    var _ := ta is (Y, Y, Y);
    var _ := ta is Triple<Y>;
    var _ := ta is TA<Y>;
    var _ := ta is TB<Y>;
    var _ := ta is TBB<Y>;
  case true =>
    var _ := tb is (int, int, int); // error
    var _ := tb is (Y, Y, Y);
    var _ := tb is Triple<Y>;
    var _ := tb is TA<Y>;
    var _ := tb is TB<Y>;
    var _ := tb is TBB<Y>;
  case true =>
    var _ := tbb is (int, int, int); // error
    var _ := tbb is (Y, Y, Y);
    var _ := tbb is Triple<Y>;
    var _ := tbb is TA<Y>;
    var _ := tbb is TB<Y>;
    var _ := tbb is TBB<Y>;
}

method AsSubsetType<Y>(t0: (Y, Y, Y), t1: Triple<Y>, ta: TA<Y>, tb: TB<Y>, tbb: TBB<Y>)
{
  if
  case true =>
    var _ := t0 as (int, int, int); // error
    var _ := t0 as (Y, Y, Y);
    var _ := t0 as Triple<Y>;
    var _ := t0 as TA<Y>;
    var _ := t0 as TB<Y>;
    var _ := t0 as TBB<Y>;
  case true =>
    var _ := t1 as (int, int, int); // error
    var _ := t1 as (Y, Y, Y);
    var _ := t1 as Triple<Y>;
    var _ := t1 as TA<Y>;
    var _ := t1 as TB<Y>;
    var _ := t1 as TBB<Y>;
  case true =>
    var _ := ta as (int, int, int); // error
    var _ := ta as (Y, Y, Y);
    var _ := ta as Triple<Y>;
    var _ := ta as TA<Y>;
    var _ := ta as TB<Y>;
    var _ := ta as TBB<Y>;
  case true =>
    var _ := tb as (int, int, int); // error
    var _ := tb as (Y, Y, Y);
    var _ := tb as Triple<Y>;
    var _ := tb as TA<Y>;
    var _ := tb as TB<Y>;
    var _ := tb as TBB<Y>;
  case true =>
    var _ := tbb as (int, int, int); // error
    var _ := tbb as (Y, Y, Y);
    var _ := tbb as Triple<Y>;
    var _ := tbb as TA<Y>;
    var _ := tbb as TB<Y>;
    var _ := tbb as TBB<Y>;
}

newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype byte = x: int | 0 <= x < 256
newtype Bits02 = x: bv8 | x & !5 == 0
newtype EvenWord = x: bv32 | x % 1 == 0

method CommonSystemsConversions() returns (i: int, n: nat, i32: int32, b: byte, bits: Bits02, e: EvenWord, ch: char)
{
  b := bits as byte;
  i := bits as int;
  e := (b as int32 + i as int32) as EvenWord;
  n := bits as nat;
  i32 := bits as int32;

  i32 := b as int32;
  b := i32 as byte;

  var u0 := bits as bv8;
  var u1 := e as bv8;
  var w := (u0 + u1) as bv16;
  e := w as EvenWord;

  ch := bits as int as char;
  i := ch as int;
  ch := i as char;
}
