// NONUNIFORM: Demonstration of the use of the external Rust Option<> type
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %baredafny run --target=rs --enforce-determinism --raw-pointers "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:compile false} {:extern "::std::option"} RustStdOption {
  // Define the Rust option type
  datatype {:extern "Option"} {:compile false} {:rust_rc false} Option<T> =
    Some({:extern "0"} {:extern_extract "unwrap"} value: T) | None {
  }
}

module RustStdCompare {
  // Define the Rust option type
  datatype {:rust_rc false} Option<T> =
    Some({:extern "0"} {:extern_extract "unwrap"} value: T) | None {
  }
}

module DatatypeTests {
  import opened RustStdOption
  import RustStdCompare

  newtype u8 = x: int | 0 <= x < 255

  // Raw Rust enum
  datatype {:rust_rc false} NoArg = OptionA | OptionB | OptionC

  // Raw Rust enum
  datatype {:rust_rc false} AlmostOption = Nothing | ThereItIs(u: u8) {
    static function default(): AlmostOption {
      ThereItIs(0 as u8)
    }
  }

  // Raw Rust enum
  datatype {:rust_rc false} AlmostOptionWrapper = StillNothing | AlmostThere(u: AlmostOption)  

  // Raw Rust enum
  datatype {:rust_rc false} GenericOption<T> = GenericNothing | GenericSome(value: T)  

  // Putting {:rust_rc false} would create a compilation issue because there should be an indirection
  datatype Peano = Zero | One(p: Peano)

  // Raw Rust struct
  datatype {:rust_rc false} Struct = StructConstructor(a: u8, b: bool) {
    function BTrue(): Struct {
      if b then this else this.(b := true)
    }
  }

  // Raw Rust enum
  datatype {:rust_rc false} Multiple =
    | ConstructorA(a: u8)
    | ConstructorB(b: bool)
    | ConstructorAB(a: u8, b: bool)
  {
    function Gather(other: Multiple): Multiple {
      match this {
        case ConstructorAB(a, b) => this
        case ConstructorA(a) =>
          if other.ConstructorB? then
            ConstructorAB(a, other.b)
          else
            this
        case ConstructorB(b) =>
          if other.ConstructorA? then
            ConstructorAB(other.a, b)
          else
            this
      }
    }
  }

  // Rc-wrapped Rust struct
  datatype RcStruct = RcStructConstructor(a: u8, b: bool) {
    function BTrue(): RcStruct {
      if b then this else this.(b := true)
    }
  }

  // Rc-wrapped Rust enum
  datatype RcMultiple =
    | RcConstructorA(a: u8)
    | RcConstructorB(b: bool)
    | RcConstructorAB(a: u8, b: bool)
  {
    function Gather(other: RcMultiple): RcMultiple {
      if RcConstructorAB? then this
      else if RcConstructorA? then
        if other.RcConstructorB? then
          RcConstructorAB(a, other.b)
        else
          this
      else if RcConstructorB? then
        if other.RcConstructorA? then
          RcConstructorAB(other.a, b)
        else
          this
      else
        this
    }
  }

  // Rc-wrapped struct
  datatype Recursive = Recursive(head: int, tail: Option<Recursive>)

  method PrintOption(o: Option<u8>) {
    match o {
      case Some(u) => print u, "\n";
      case None => print "None\n";
    }
  }

  method Main() {
    var n: NoArg := OptionA;
    n := OptionB;
    expect !n.OptionC?;

    var d: AlmostOption := Nothing;
    d := ThereItIs(4 as u8);

    var p: Peano := Zero;
    p := One(p);
    var q: Peano := p;
    p := One(p);
    q := One(q);
    expect p == q;

    var c := ConstructorA(0); // Raw struct creation
    c := c.(a := 2);  // Since the variable is the same and c owns the value, we can update in place.
    c := c.Gather(ConstructorA(1)); // Ignored
    expect c.ConstructorA? && !c.ConstructorB? && !c.ConstructorAB?;
    expect c.a == 2;
    c := c.Gather(ConstructorB(true));
    expect c.ConstructorAB? && !c.ConstructorA? && !c.ConstructorB?;
    expect c.a == 2 && c.b;
    var a := StructConstructor(1, false);
    expect a.BTrue() == StructConstructor(1, true);

    var c2 := RcConstructorA(0); // Raw struct creation
    c2 := c2.(a := 2);  // Since the variable is the same and c owns the value, we can update in place.
    c2 := c2.Gather(RcConstructorA(1)); // Ignored
    expect c2.RcConstructorA? && !c2.RcConstructorB? && !c2.RcConstructorAB?;
    c2 := c2.Gather(RcConstructorB(true));
    expect c2.RcConstructorAB? && !c2.RcConstructorA? && !c2.RcConstructorB?;
    var rc_a := RcStructConstructor(1, false);
    expect rc_a.BTrue() == RcStructConstructor(1, true);

    var r := Recursive(0, None);
    r := Recursive(1, Some(r));
    print r, "\n"; // Recursive(1, Some(Recursive(0, None)))
    
    // Interfacing with native types
    var x := Some(3 as u8);
    var u := x.value;
    expect u == 3;
    match x {
      case Some(i) =>
        expect i == 3;
    }
    expect x.value == 3;
    PrintOption(x);
    PrintOption(None);
    print x, "\n";
    var no: Option<u8> := None;
    print no, "\n";

    var homeMadeOption := RustStdCompare.Some(3);
    if homeMadeOption.Some? {
      print homeMadeOption.value, "\n";
    }
    homeMadeOption := RustStdCompare.None;
  }
}