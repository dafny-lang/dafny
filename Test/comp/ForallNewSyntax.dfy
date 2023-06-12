// RUN: %baredafny verify %args --relax-definite-assignment --function-syntax:3 --quantifier-syntax:4 "%s" > "%t"
// RUN: %baredafny run %args --function-syntax:3 --quantifier-syntax:4 --no-verify --target:cs "%s" >> "%t"
// RUN: %baredafny run %args --function-syntax:3 --quantifier-syntax:4 --no-verify --target:js "%s" >> "%t"
// RUN: %baredafny run %args --function-syntax:3 --quantifier-syntax:4 --no-verify --target:go "%s" >> "%t"
// RUN: %baredafny run %args --function-syntax:3 --quantifier-syntax:4 --no-verify --target:java "%s" >> "%t"
// RUN: %baredafny run %args --function-syntax:3 --quantifier-syntax:4 --no-verify --target:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var arrayTests := new ArrayTests();
  arrayTests.Run();

  var multiArrayTests := new MultiArrayTests();
  multiArrayTests.Run();

  var objectTests := new ObjectTests();
  objectTests.Run();
}

class ArrayTests {
  var a: array<int>
  var b: array<int>

  predicate Valid() reads this, a, b {
    a.Length == 5 && b.Length == 5
  }

  constructor() ensures fresh(a) && fresh(b) && Valid() {
    a := new int[5];
    b := new int[5];
  }

  method Initialize() modifies a, b {
    forall i | 0 <= i < a.Length {
      a[i] := i;
    }
    forall i | 0 <= i < b.Length {
      b[i] := i;
    }
  }

  method Run() modifies a, b requires Valid() ensures Valid() {
    BasicCases();
    WrongIndex();
    SequenceConversion();
    IndexCollection();
    Functions();
  }

  method BasicCases() modifies a, b requires Valid() ensures Valid() {
    print "Arrays: Basic cases\n";

    // Can sequentialize (compile as single loop):
    forall i | 0 <= i < a.Length {
      a[i] := i;
    }
    print a[..], "\n"; // [ 0, 1, 2, 3, 4 ];

    // Can sequentialize
    forall i | 0 <= i < a.Length {
      b[i] := a[i];
    }
    print b[..], "\n"; // [ 0, 1, 2, 3, 4 ];

    // Can sequentialize
    forall i | 0 <= i < a.Length && a[i] % 2 == 0 {
      a[i] := a[i] * 2;
    }
    print a[..], "\n"; // [ 0, 1, 4, 3, 8 ];
  }

  method WrongIndex() modifies a, b requires Valid() ensures Valid() {
    print "\nArrays: Wrong index\n";

    // Can't sequentialize: different index in RHS
    Initialize();
    forall i | 1 <= i < a.Length {
      a[i] := a[i - 1];
    }
    print a[..], "\n"; // [ 0, 0, 1, 2, 3 ];

    // Can't sequentialize: different index in LHS
    Initialize();
    forall i | 0 <= i < a.Length - 1 {
      a[i + 1] := a[i];
    }
    print a[..], "\n"; // [ 0, 0, 1, 2, 3 ];

    // Can't sequentialize: wrong array access in range
    Initialize();
    forall i | 0 <= i < a.Length && (i == 0 || i != a[0]) {
      a[i] := a[i] + 1;
    }
    print a[..], "\n"; // [ 1, 2, 3, 4, 5 ]
  }

  method SequenceConversion() modifies a, b requires Valid() ensures Valid() {
    print "\nArrays: Sequence conversion\n";

    // Can't sequentialize: sequence conversion in range
    Initialize();
    forall i | 0 <= i < a.Length && (i == 0 || i !in a[..2]) {
      a[i] := a[i] + 2;
    }
    print a[..], "\n"; // [ 2, 1, 4, 5, 6 ]

    // Can't sequentialize: sequence conversion in RHS
    Initialize();
    forall i | 1 <= i < a.Length - 1 {
      a[i] := |a[i-1..i+2]|;
    }
    print a[..], "\n"; // [ 0, 3, 3, 3, 4 ]
  }

  method IndexCollection() modifies a, b requires Valid() ensures Valid() {
    print "\nArrays: Index collection\n";

    // Can sequentialize: range collection passes through UniqueValues()
    Initialize();
    forall i <- [ 0, 0, 0 ] {
      a[i] := a[i] + 1;
    }
    print a[..], "\n"; // [ 1, 1, 2, 3, 4 ]

    // Can sequentialize
    Initialize();
    forall i <- { 0, 0, 0 } {
      a[i] := a[i] + 1;
    }
    print a[..], "\n"; // [ 1, 1, 2, 3, 4 ]

    // TODO add case that can't be sequentialized
  }

  method Functions() modifies a, b requires Valid() ensures Valid() {
    print "\nArrays: Functions\n";

    var f: int -> int := x => x + 1;

    // Can sequentialize: function is pure
    Initialize();
    forall i | 0 <= i < a.Length && a[i] != f(0) {
      a[i] := f(a[i]);
    }
    print a[..], "\n"; // [ 1, 1, 3, 4, 5 ];

    // Can sequentialize: function is pure
    Initialize();
    forall i | 0 <= i < a.Length && a[i] != f(0) {
      a[i] := f(a[i]);
    }
    print a[..], "\n"; // [ 1, 1, 3, 4, 5 ];

    var g: int ~> int := x reads this, a, b requires Valid() => x + a[1];

    // Can't sequentialize: impure function call in range
    Initialize();
    forall i | 0 <= i < a.Length && a[i] != g(2) {
      a[i] := i + 1;
    }
    print a[..], "\n"; // [ 1, 2, 3, 3, 5 ]

    // Can't sequentialize: impure function call in RHS
    Initialize();
    forall i | 0 <= i < a.Length {
      a[i] := g(i);
    }
    print a[..], "\n"; // [ 1, 2, 3, 4, 5 ]
  }
}

class MultiArrayTests {
  var a: array2<int>

  predicate Valid() reads this, a {
    a.Length0 == 3 && a.Length1 == 3
  }

  constructor() ensures fresh(a) && Valid() {
    a := new int[3,3];
  }

  function method StateAsSeq(): seq<seq<int>> reads this, a requires Valid() {
    [ [ a[0,0], a[0,1], a[0,2] ],
      [ a[1,0], a[1,1], a[1,2] ],
      [ a[2,0], a[2,1], a[2,2] ] ]
  }

  method Report() requires Valid() ensures Valid() {
    print StateAsSeq(), "\n";
  }

  method Run() modifies a requires Valid() ensures Valid() {
    print "\nMulti-dimensional arrays\n";

    // Can sequentialize
    forall i | 0 <= i < a.Length0, 
           j | 0 <= j < a.Length1 
    {
      a[i,j] := i + 2 * j;
    }
    Report(); // [[0, 2, 4], [1, 3, 5], [2, 4, 6]]

    // Can't sequentialize
    forall i | 0 <= i < a.Length0, 
           j | 0 <= j < a.Length1
    {
      a[i,j] := a[j,i];
    }
    Report(); // [[0, 1, 2], [2, 3, 4], [4, 5, 6]];
  }
}

class Thing {
  var i: int
  var r: real
  var t: Thing?

  constructor(i: int, r: real, t: Thing?) ensures this.i == i && this.r == r && this.t == t {
    this.i := i;
    this.r := r;
    this.t := t;
  }

  method Print() {
    print "(", i, ", ", r, ")";
  }

  static method PrintMany(things: seq<Thing>) {
    print "[";
    var i := 0;
    var sep := "";
    while i < |things| decreases |things| - i {
      print sep;
      things[i].Print();
      i := i + 1;
      sep := ", ";
    }
    print "]";
  }
}

class ObjectTests {
  var thing1: Thing, thing2: Thing, thing3: Thing

  predicate Valid() reads this {
    thing1 != thing2 && thing1 != thing3 && thing2 != thing3
  }

  constructor() ensures fresh(thing1) && fresh(thing2) && fresh(thing3) && Valid() {
    thing1 := new Thing(1, 1.0, null);
    thing2 := new Thing(2, 2.0, null);
    thing3 := new Thing(3, 3.0, null);
  }

  method Initialize() modifies thing1, thing2, thing3 requires Valid() ensures Valid() {
    thing1.i := 1; thing1.r := 1.0; thing1.t := null;
    thing2.i := 2; thing2.r := 2.0; thing2.t := null;
    thing3.i := 3; thing3.r := 3.0; thing3.t := null;
  }

  method Report() {
    Thing.PrintMany([ thing1, thing2, thing3 ]);
    print "\n";
  }

  method Run() modifies thing1, thing2, thing3 requires Valid() ensures Valid() {
    BasicCases();
    BadFieldAccesses();
    Functions();
  }

  method BasicCases() modifies thing1, thing2, thing3 requires Valid() ensures Valid() {
    print "\nObjects: Basic cases\n";
    var things: seq<Thing> := [ thing1, thing2, thing3 ];

    // Can sequentialize
    Initialize();
    forall t <- things {
      t.i := 0;
    }
    Report(); // [(0, 1.0), (0, 2.0), (0, 3.0)]

    // Can sequentialize
    Initialize();
    forall t <- things | t.r != 2.0 {
      t.i := t.i + 1;
    }
    Report(); // [(2, 1.0), (2, 2.0), (4, 3.0)]

    // Can sequentialize
    Initialize();
    forall t <- things | t.i != 3 {
      t.i := t.i + 1;
    }
    Report(); // [(2, 1.0), (3, 2.0), (3, 3.0)]
  }

  method BadFieldAccesses() modifies thing1, thing2, thing3 requires Valid() ensures Valid() {
    print "\nObjects: Bad field accesses\n";
    var things: seq<Thing> := [ thing1, thing2, thing3 ];

    // Can't sequentialize: bad field access in range
    Initialize();
    thing2.t := thing1;
    forall t <- things | (t.t == null || t.t.i == 1) {
      t.i := t.i + 1;
    }
    Report(); // [(2, 1.0), (3, 2.0), (4, 3.0)]

    // Can't sequentialize: bad field access in RHS
    Initialize();
    forall t <- things {
      t.i := thing1.i + 1;
    }
    Report(); // [(2, 1.0), (2, 2.0), (2, 3.0)]

    // Can't sequentialize: wrong object in update
    Initialize();
    thing1.t := thing3;
    thing2.t := thing1;
    thing3.t := thing2;
    forall t <- things {
      t.t.i := t.i;
    }
    Report(); // [(2, 1.0), (3, 2.0), (1, 3.0)]
  }

  method Functions() modifies thing1, thing2, thing3 requires Valid() ensures Valid() {
    print "\nObjects: Functions\n";
    var things: seq<Thing> := [ thing1, thing2, thing3 ];

    var f: int -> int := x => x * 2;

    // Can sequentialize: function is pure
    Initialize();
    forall t <- things {
      t.i := f(t.i);
    }
    Report(); // [(2, 1.0), (4, 2.0), (6, 3.0)]

    var g: () ~> int := () reads this, thing2 => thing2.i;

    // Can't sequentialize: impure function call in range
    Initialize();
    forall t <- things | t.i + g() != 5 {
      t.i := t.i + 1;
    }
    Report(); // [(2, 1.0), (3, 2.0), (3, 3.0)]

    // Can't sequentialize: impure function call in RHS
    Initialize();
    forall t <- things {
      t.i := t.i + g();
    }
    Report(); // [(3, 1.0), (4, 2.0), (5, 3.0)];
  }
}
