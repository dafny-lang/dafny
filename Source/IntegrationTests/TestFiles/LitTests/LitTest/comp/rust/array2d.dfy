// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var a := new int[3, 4] ((i,j) => 0);

  print_array2d(a);

  a[0, 0] := 1;
  a[0, 1] := 2;
  a[0, 2] := 3;
  a[0, 3] := 4;

  a[1, 0] := 5;
  a[1, 1] := 6;
  a[1, 2] := 7;
  a[1, 3] := 8;

  a[2, 0] := 9;
  a[2, 1] := 10;
  a[2, 2] := 11;
  a[2, 3] := 12;

  print_array2d(a);

  a[2, 3], a[0, 0] := a[0, 0], a[2, 3];
  
  print_array2d(a);
}

method print_array2d(arr: array2<int>) {
  print "[\n";
  for i := 0 to arr.Length0 {
    print "  [";
    for j := 0 to arr.Length1 {
      print arr[i,j];
      if j < arr.Length1 - 1 {
        print ", ";
      }
    }
    print "]";
    if i < arr.Length0 - 1 {
      print ",\n";
    } else {
      print "\n";
    }
  }
  print "]\n";
}
