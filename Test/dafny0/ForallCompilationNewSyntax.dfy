// RUN: %baredafny run %args --relax-definite-assignment --quantifier-syntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var c := new MyClass;
  c.arr := new int[10,20];
  c.K0(3, 12);
  c.K1(3, 12);
  c.K2(3, 12);
  c.K3(3, 12);
  c.K4(12);
  c.M();
  c.N();
  c.P();
  c.Q();
}

class MyClass
{
  var arr: array2<int>

  method K0(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    forall k <- {-3, 4} {
      arr[i,j] := 50;
    }
  }

  method K1(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    // note the absence of a modifies clause
  {
    forall k <- {} {
      arr[i,j] := k;  // fine, since control will never reach here
    }
  }

  method K2(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    forall k <- {-3, 4} {
      // The following would have been an error (since this test file tests
      // compilation, we don't include the test here):
      // arr[i,j] := k;  // error: k can take on more than one value
    }
  }

  method K3(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    forall k: nat <- {-3, 4} | k <= i {
      arr[k,j] := 50;  // fine, since k:nat is at least 0
    }
  }

  method K4(j: int)
    requires 0 <= j < arr.Length1
    modifies arr
  {
    forall i | 0 <= i < arr.Length0, k: nat <- {-3, 4} {
      arr[i,j] := k;  // fine, since k can only take on one value
    }
  }

  method M()
  {
    var ar := new int [3,3];
    var S: set<int> := {2,0};
    forall k | k in S {
      ar[k,1]:= 0;
    }
    forall k <- S, j <- S {
      ar[k,j]:= 0;
    }
  }

  method N() {
    var ar := new int[3, 3];
    ar[2,2] := 0;
  }

  method P() {
    var ar := new int[3];
    var prev := ar[..];
    var S: set<int> := {};
    forall k <- S {
      ar[k] := 0;
    }
    assert ar[..] == prev;
  }

  method Q() {
    var ar := new int[3,3];
    var S: set<int> := {1,2};
    forall k <- S {
      ar[0,0] := 0;
    }
    assert ar[0,0] == 0;
  }
}
