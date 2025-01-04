// RUN: %exits-with 4 %verify --allow-deprecation --unicode-char false --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


// Check every possible conversion range error among int,char,bv,real,ORDINAL

// int to char
method Test1(n: int)
{
  var ch := n as char;  // ERROR
}

method Test1b(n: int)
  requires n < 65536
{
  var ch := n as char;  // ERROR
}

method Test1c(n: int)
  requires 0 <= n
{
  var ch := n as char;  // ERROR
}

method Test1OK(n: int)
  requires 0 <= n < 65536
{
  var ch := n as char;
}


// int to ORDINAL
method Test2(n: int) {
  var o: ORDINAL := n as ORDINAL;  // ERROR
}

method Test2OK(n: int)
  requires n >= 0
{
  var o: ORDINAL := n as ORDINAL;
}

// real to ORDINAL
method Test3(r: real)
  requires r.Floor as real == r
{
  var o: ORDINAL := r as ORDINAL;  // ERROR
}

method Test3b(r: real)
  requires r >= 0.0  // ERROR
{
  var o: ORDINAL := r as ORDINAL;
}

method Test3OK(r: real)
  requires r.Floor as real == r
  requires r >= 0.0
{
  var o: ORDINAL := r as ORDINAL;
}

// real to int
method Test4(r: real)
{
  var n: int := r as int;  // ERROR
}

method Test4OK(r: real)
  requires r.Floor as real == r
{
  var n: int := r as int;
}

// real to char
method Test5(r:real)
  requires 0.0 <= r
  requires r == r.Floor as real
{
  var ch := r as char;  // ERROR
}

method Test5b(r:real)
  requires r <= 65535.0
  requires r == r.Floor as real
{
  var ch := r as char;  // ERROR
}

method Test5c(r:real)
  requires 0.0 <= r <= 65535.0
{
  var ch := r as char;  // ERROR
}

method Test5OK(r: real)
  requires 0.0 <= r < 65536.0
  requires r == r.Floor as real
{
  var ch := r as char;
}

// real to bv
method Test6(r: real)
  requires 0.0 <= r
  requires r == r.Floor as real
{
  var bv := r as bv8;  // ERROR
}

method Test6b(r: real)
  requires r <= 255.0
  requires r == r.Floor as real
{
  var bv := r as bv8;  // ERROR
}

method Test6c(r: real)
  requires 0.0 <= r <= 255.0
{
  var bv := r as bv8;  // ERROR
}

method Test6OK(r: real)
  requires 0.0 < r <= 255.0
  requires r == r.Floor as real
{
  var bv := r as bv8;
}

// int to bv
method Test7(n: int)
  requires 0 <= n
{
  var bv := n as bv8;  // ERROR
}

method Test7b(n: int)
  requires n <= 255
{
  var bv := n as bv8;  // ERROR
}

method Test7OK(n: int)
  requires 0 <= n <= 255
{
  var bv := n as bv8;
}

// char to bv
method Test8(n: char)
{
  var bv := n as bv8;  // ERROR
}

method Test8OK(n: char)
  requires n as int <= 255
{
  var bv := n as bv8;
}

method Test8OKb(n: char)
{
  var bv := n as bv16;
}

// ordinal to char
method TestA(o: ORDINAL)
{
  var ch := o as char;  // ERROR
}

method TestAb(o: ORDINAL)
  requires o.IsNat
{
  var ch := o as char;  // ERROR
}

method TestAOK(o: ORDINAL)
  requires o.IsNat && o as int < 65536
{
  var ch := o as char;
}


// ordinal to bv
method TestB(o: ORDINAL)
{
  var b := o as bv8;  // ERROR
}

method TestBb(o: ORDINAL)
  requires o.IsNat
{
  var b := o as bv8;  // ERROR
}

method TestBOK(o: ORDINAL)
  requires o.IsNat && o as int < 256
{
  var b := o as bv8;
}

// bv to char
method TestC(b: bv32)
{
  var ch := b as char;  // ERROR
}

method TestCOK(b: bv32)
  requires b as int < 65536
{
  var ch := b as char;
}
method TestCOKb(b: bv16)
{
  var ch := b as char;
}
method TestCOKc(b: bv8)
{
  var ch := b as char;
}
