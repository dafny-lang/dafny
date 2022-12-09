// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Types {
  datatype XY =
    | {:testAttr0} D0(x: int)
    | ghost {:testAttr1} G0(y: bool)
    | ghost G1(y: bool, z: real, w: char)
    | {:testAttr2} D1(z: real)

  datatype Wrapper<A> = Wrapper(A)
}

module Ghost {
  import opened Types

  method M0(xy: XY) {
    var x := xy.D0? && xy.x == 3;
    ghost var y := xy.G0? && xy.y;
    var yy;
    yy := xy.G0? && xy.y; // error (x2): RHS is ghost, but LHS is not
  }

  method M1(xy: XY)
    requires xy.G1?
  {
    // Even though the verifier will forbid use of .y and .w in compiled contexts,
    // the resolver allows them.
    var y, z, w;
    y := xy.y; // error: .y implies a ghost constructor
    w := xy.w; // error: .w implies a ghost constructor
    z := xy.z;

    ghost var a, b, c;
    a := xy.y;
    b := xy.w;
    c := xy.z;
  }

  method M2(ghost xy: XY)
    requires xy.G1?
  {
    var y, z, w;
    y := xy.y; // error: RHS is ghost, but LHS is not
    w := xy.w; // error: RHS is ghost, but LHS is not
    z := xy.z; // error: RHS is ghost, but LHS is not

    ghost var a, b, c;
    a := xy.y;
    b := xy.w;
    c := xy.z;
  }
}

module {:options "/functionSyntax:4"} Match {
  import opened Types

  method M0(xy: XY) returns (r: int) {
    match xy
    case any => r := 0;
  }

  method M1(xy: XY) returns (r: int) {
    match xy
    case any =>
  }

  method M2(w: Wrapper<XY>) returns (r: int) {
    match w
    case Wrapper(any) => r := 0;
  }

  method M3(w: Wrapper<XY>) returns (r: int) {
    match w
    case Wrapper(_) => r := 0;
  }

  method M4(w: Wrapper<XY>) returns (r: int) {
    match w
    case _ => r := 0;
  }

  method P0(xy: XY) returns (r: int) {
    // the following match statement is ghost, because it indirectly mentions a ghost constructor of type XY
    match xy
    case D0(_) => r := 0; // error: assignment to r in a ghost context
    case any =>
  }

  method P1(xy: XY) returns (r: int) {
    // the following match statement is ghost, because it indirectly mentions a ghost constructor of type XY
    match xy
    case D0(_) =>
    case any =>
  }

  method P2(w: Wrapper<XY>) returns (r: int) {
    match w
    case Wrapper(_) => r := 0;
  }

  method P3(w: Wrapper<XY>) returns (r: int) {
    // the following match statement is ghost, because it mentions a constructor of type XY
    match w
    case Wrapper(D0(_)) =>
    case Wrapper(_) => r := 0; // error: assignment to r in a ghost context
  }

  function F0(xy: XY): int {
    match xy
    case any => 0
  }

  ghost function F1(xy: XY): int {
    match xy
    case any => 0
  }

  function F2(w: Wrapper<XY>): int {
    match w
    case Wrapper(any) => 0
  }

  function F3(w: Wrapper<XY>): int {
    match w
    case Wrapper(_) => 0
  }

  function F4(w: Wrapper<XY>): int {
    match w
    case _ => 0
  }

  function G0(xy: XY): int {
    match xy
    case D0(_) => 0
    case _ => 0 // error: this case depends on a ghost constructor
  }

  ghost function G1(xy: XY): int {
    // in a ghost context, this match expression is allowed
    match xy
    case D0(_) => 0
    case _ => 0
  }

  function G2(w: Wrapper<XY>): int {
    match w
    case Wrapper(_) => 0
  }

  function G3(w: Wrapper<XY>): int {
    match w
    case Wrapper(D0(_)) => 0
    case Wrapper(_) => 0 // error: this case depends on a ghost constructor
  }

  method H0(xy: XY) returns (r: int) {
    // the following match expression is ghost, because it depends on a ghost constructor
    var a :=
      match xy
      case D0(_) => 0
      case _ => 0;
    return a; // error: a is ghost
  }

  ghost method H1(xy: XY) returns (r: int) {
    var a :=
      match xy
      case D0(_) => 0
      case _ => 0;
    return a;
  }

  method H2(w: Wrapper<XY>) returns (r: int) {
    var a :=
      match w
      case Wrapper(_) => 0;
    return a;
  }

  method H3(w: Wrapper<XY>) returns (r: int) {
    // the following match expression is ghost, because it depends on a ghost constructor
    var a :=
      match w
      case Wrapper(D0(_)) => 0
      case Wrapper(_) => 0;
    return a; // error: a is ghost
  }

  method H4(xy: XY) returns (r: int) {
    var a :=
      match xy
      case _ => 0;
    return a;
  }
}

module {:options "/functionSyntax:4"} EqualitySupport {
  import opened Types

  method M(xy: XY) returns (a: int) {
    if xy == xy { // this is okay, because the "if" statement is ghost
    }

    if xy == xy { // this is fine (but the verifier would give an error)
      a := 3;
    }

    if Eq(xy, xy) { // error: XY does not support equality
      a := 4;
    }
  }

  function Eq<T(==)>(x: T, y: T): bool {
    x == y
  }
}

module {:options "/functionSyntax:4"} Constructors {
  import opened Types

  method M0() returns (xy0: XY, ghost xy1: XY) {
    xy0 := D0(2);
    xy0 := D1(2.0);
    xy0 := G0(true); // error: G0 is a ghost constructor

    xy1 := D0(2);
    xy1 := D1(2.0);
    xy1 := G0(true);
  }

  method M1() returns (xy0: XY, ghost xy1: XY) {
    var a := D0(2);
    var b := D1(2.0);
    var c := G0(true); // this makes c auto-ghost

    xy0 := a;
    xy0 := b;
    xy0 := c; // error: RHS is ghost
    xy1 := a;
    xy1 := b;
    xy1 := c;
  }

  function F(b: bool): XY {
    if b then
      D0(2)
    else
      G0(true) // error: G0 is a ghost constructor
  }
}

module StmtExpr {
  import opened Types

  method CompiledMethod(xy: XY) returns (a: int) {
    a :=
      calc {
        0;
      ==  { // we're in a ghost context, so the following match constructs are allowed
            var x;
            x := match xy
                case D0(_) => 0
                case _ => 0;
            match xy
            case D0(_) => x := 0;
            case any =>
          }
        0;
      ==  { if xy.G1? { } else { } }
        0;
      }
      20;
  }
}

module Updates {
  datatype D =
    | D0(c: int, n: int)
    | ghost D1(c: int, x: int)
    | ghost D2(c: int, x: int, y: int)
    | ghost D3(c: int, x: int, y: int)

  method Select0(d: D) returns (r: int)
  {
    r := d.c; // one constructor enclosing .c is non-ghost, so this is fine
    r := d.n;
    r := d.x; // error: RHS is ghost, LHS is not
    r := d.y; // error: RHS is ghost, LHS is not
  }

  method Update0(d: D) returns (r: D)
  {
    r := d.(c := 2); // one constructor enclosing .c is non-ghost, so this is fine
    r := d.(n := 2);
    r := d.(x := 2); // error: RHS is ghost, LHS is not
    r := d.(y := 2); // error: RHS is ghost, LHS is not

    r := d.(c := 2, x := 2); // error: RHS is ghost, LHS is not
    r := d.(c := 2, n := 2);
    r := d.(x := 2, y := 2); // error: RHS is ghost, LHS is not
  }

  method Select1(d: D) returns (r: int)
  {
    var a := d.c;
    var b := d.n;
    var c := d.x;
    var e := d.y;

    r := a;
    r := b;
    r := c; // error: RHS is ghost, LHS is not
    r := e; // error: RHS is ghost, LHS is not
  }

  method Update1(d: D) returns (r: D)
  {
    var a := d.(c := 2);
    var b := d.(n := 2);
    var c := d.(x := 2);
    var e := d.(y := 2);

    var f := d.(c := 2, x := 2);
    var g := d.(c := 2, n := 2);
    var h := d.(x := 2, y := 2);

    r := a;
    r := b;
    r := c; // error: RHS is ghost, LHS is not
    r := e; // error: RHS is ghost, LHS is not
    r := f; // error: RHS is ghost, LHS is not
    r := g;
    r := h; // error: RHS is ghost, LHS is not
  }
}

module {:options "/functionSyntax:4"} EnumTests0 {
  datatype Enum = ghost EnumA | EnumB
  {
    predicate P() {
      this != EnumA // error: ghost constructor not allowed in compiled code
    }
  }

  datatype TotallyGhost = ghost Ctor0 | ghost Ctor1
  {
    predicate P() {
      this != Ctor0 // error: ghost constructor not allowed in compiled code
    }
  }
}

module {:options "/functionSyntax:4"} EnumTests1 {
  datatype Enum = ghost EnumA | EnumB
  {
    predicate P() {
      this == this // the resolver is fine with this, but the verifier will complain
    }
    predicate Q() {
      this != EnumB // the resolver is fine with this, but the verifier will complain
    }
  }

  datatype TotallyGhost = ghost Ctor0 | ghost Ctor1
  {
    predicate P() {
      this == this // error: ghost equality not allowed in compiled code
    }
  }
}
