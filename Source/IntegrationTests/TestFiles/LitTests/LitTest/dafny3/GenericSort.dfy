// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module TotalOrder {
  type T // the type to be compared
  predicate Leq(a: T, b: T) // Leq(a,b) iff a <= b
  // Three properties of total orders.  Here, they are given as unproved
  // lemmas, that is, as axioms.
  lemma Antisymmetry(a: T, b: T)
    requires Leq(a, b) && Leq(b, a)
    ensures a == b
  lemma Transitivity(a: T, b: T, c: T)
    requires Leq(a, b) && Leq(b, c)
    ensures Leq(a, c)
  lemma Totality(a: T, b: T)
    ensures Leq(a, b) || Leq(b, a)
}

abstract module Sort {
  import O : TotalOrder  // let O denote some module that has the members of TotalOrder

  ghost predicate Sorted(a: array<O.T>, low: int, high: int)
    requires 0 <= low <= high <= a.Length
    reads a
    // The body of the predicate is hidden outside the module, but the postcondition is
    // "exported" (that is, visible, known) outside the module.  Here, we choose the
    // export the following property:
    ensures Sorted(a, low, high) ==> forall i, j :: low <= i < j < high ==> O.Leq(a[i], a[j])
  {
    forall i, j :: low <= i < j < high ==> O.Leq(a[i], a[j])
  }

  // In the insertion sort routine below, it's more convenient to keep track of only that
  // neighboring elements of the array are sorted...
  ghost predicate NeighborSorted(a: array<O.T>, low: int, high: int)
    requires 0 <= low <= high <= a.Length
    reads a
  {
    forall i :: low < i < high ==> O.Leq(a[i-1], a[i])
  }
  // ...but we show that property to imply all pairs to be sorted.  The proof of this
  // lemma uses the transitivity property.
  lemma NeighborSorted_implies_Sorted(a: array<O.T>, low: int, high: int)
    requires 0 <= low <= high <= a.Length
    requires NeighborSorted(a, low, high)
    ensures Sorted(a, low, high)
    decreases high - low
  {
    if low != high {
      NeighborSorted_implies_Sorted(a, low+1, high);
      forall j | low+1 < j < high
      {
        O.Transitivity(a[low], a[low+1], a[j]);
      }
    }
  }

  // Standard insertion sort method
  method InsertionSort(a: array<O.T>)
    modifies a
    ensures Sorted(a, 0, a.Length)
    ensures multiset(a[..]) == old(multiset(a[..]))
  {
    if a.Length == 0 { return; }
    var i := 1;
    while i < a.Length
      invariant 0 < i <= a.Length
      invariant NeighborSorted(a, 0, i)
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      var j := i;
      while 0 < j && !O.Leq(a[j-1], a[j])
        invariant 0 <= j <= i
        invariant NeighborSorted(a, 0, j)
        invariant NeighborSorted(a, j, i+1)
        invariant 0 < j < i ==> O.Leq(a[j-1], a[j+1])
        invariant multiset(a[..]) == old(multiset(a[..]))
      {
        // The proof of correctness uses the totality property here.
        // It implies that if two elements are not previously in
        // sorted order, they will be after swapping them.
        O.Totality(a[j-1], a[j]);
        a[j], a[j-1] := a[j-1], a[j];
        j := j - 1;
      }
      i := i + 1;
    }
    NeighborSorted_implies_Sorted(a, 0, a.Length);
  }
}

// Natural ordering of the integers
module IntOrder refines TotalOrder {
  // Instantiate type T with a datatype wrapper around an integer.
  // (If there were type synonyms, we could perhaps have written just "type T = int".)
  datatype T = Int(i: int)
  // Define the ordering on these integers
  predicate Leq ...
    ensures Leq(a, b) ==> a.i <= b.i
  {
    a.i <= b.i
  }
  // The three required properties of the order are proved here as lemmas.
  // The proofs are automatic and don't require any further assistance.
  lemma Antisymmetry ... { }
  lemma Transitivity ... { }
  lemma Totality ... { }
}

// Another example of a TotalOrder. Now we can sort pairs of integers.
// Lexiographic ordering of pairs of integers
module IntLexOrder refines TotalOrder {
  datatype T = Int(i: int, j: int)
  predicate Leq ... {
    if a.i < b.i then true
    else if a.i == b.i then a.j <= b.j
    else false
  }
  lemma Antisymmetry ... { }
  lemma Transitivity ... { }
  lemma Totality ... { }
}


// A test harness.
module Client {
  module IntSort refines Sort {  // this creates a new sorting module, like Sort by fully revealing O to be IntOrder
    import O = IntOrder
  }
  import I = IntOrder
  method TheMain() {
     var a := new I.T[4];
     a[0] := I.T.Int(6);  // alternatively, we could have written the RHS as:  IntSort.O.T.Int(6)
     a[1] := I.T.Int(1);
     a[2] := I.T.Int(0);
     a[3] := I.T.Int(4);
     // These are now the elements of the array:
     assert a[..] == [I.T.Int(6), I.T.Int(1), I.T.Int(0), I.T.Int(4)];
     // Call the sorting routine to sort the array
     IntSort.InsertionSort(a);
     // Check the answer
     assert IntSort.O.Leq(a[0], a[1]);  // lemma
     assert IntSort.O.Leq(a[1], a[2]);  // lemma
     assert IntSort.O.Leq(a[2], a[3]);  // lemma
     assert a[..] == [I.T.Int(0), I.T.Int(1), I.T.Int(4), I.T.Int(6)];
     // why not print out the result!
     print a[..], "\n";
  }
}

// ----- Now for the actual 'int' type -----

module intOrder refines TotalOrder {
  // Instantiate type T with a datatype wrapper around an integer.
  type T = int
  // Define the ordering on these integers
  predicate Leq ...
    ensures Leq(a, b) ==> a <= b
  {
    a <= b
  }
  // The three required properties of the order are proved here as lemmas.
  // The proofs are automatic and don't require any further assistance.
  lemma Antisymmetry ... { }
  lemma Transitivity ... { }
  lemma Totality ... { }
}

module AnotherClient {
  module intSort refines Sort {
    import O = intOrder
  }
  import I = intOrder
  method TheMain() {
    var a := new int[4];  // alternatively, could have written 'new I.T[4]'
    a[0] := 6;
    a[1] := 1;
    a[2] := 0;
    a[3] := 4;
    // These are now the elements of the array:
    assert a[..] == [6, 1, 0, 4];
    // Call the sorting routine to sort the array
    intSort.InsertionSort(a);
    // Check the answer
    assert intSort.O.Leq(a[0], a[1]);  // lemma
    assert intSort.O.Leq(a[1], a[2]);  // lemma
    assert intSort.O.Leq(a[2], a[3]);  // lemma
    assert a[..] == [0, 1, 4, 6];
    // why not print out the result!
    print a[..], "\n";
  }
}

method Main() {
  Client.TheMain();
  AnotherClient.TheMain();
}
