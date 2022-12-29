// RUN: %baredafny run %args --target=cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = i:int | 0 <= i < 0x100000000

method returnANullArray() returns (a: array?<uint32>)
  ensures a == null
{
  a := null;
}

method returnANonNullArray() returns (a: array?<uint32>)
  ensures a != null
  ensures a.Length == 5
{
  a := new uint32[5];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 4;
  a[4] := 5;
}

method LinearSearch(a: array<uint32>, len:uint32, key: uint32) returns (n: uint32)
  requires a.Length == len as int
  ensures 0 <= n <= len
  ensures n == len || a[n] == key
{
  n := 0;
  while n < len
    invariant n <= len
  {
    if a[n] == key {
      return;
    }
    n := n + 1;
  }
}

method PrintArray<A>(a:array?<A>, len:uint32)
  requires a != null ==> len as int == a.Length
{
  if (a == null) {
    print "It's null\n";
  } else {
    var i:uint32 := 0;
    while i < len {
      print a[i], " ";
      i := i + 1;
    }
    print "\n";
  }
}

datatype ArrayDatatype = AD(ar: array<uint32>)

method Main() {
  var a := new uint32[23];
  var i := 0;
  while i < 23 {
    a[i] := i;
    i := i + 1;
  }
  PrintArray(a, 23);
  var n := LinearSearch(a, 23, 17);
  print n, "\n";
  var s : seq<uint32> := a[..];
  print s, "\n";
  s := a[2..16];
  print s, "\n";
  s := a[20..];
  print s, "\n";
  s := a[..8];
  print s, "\n";

  // Conversion to sequence should copy elements (sequences are immutable!)
  a[0] := 42;
  print s, "\n";

  PrintArray<uint32>(null, 0);

  print "Null array:\n";
  var a1 := returnANullArray();
  PrintArray<uint32>(a1, 5);

  print "Non-Null array:\n";
  var a2 := returnANonNullArray();
  PrintArray<uint32>(a2, 5);

  print "Array in datatype:\n";
  var someAr := new uint32[3];
  someAr[0] := 1;
  someAr[1] := 3;
  someAr[2] := 9;
  var ad := AD(someAr);
  PrintArray<uint32>(ad.ar, 3);
}


