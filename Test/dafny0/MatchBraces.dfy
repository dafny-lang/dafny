// RUN: %dafny /compile:0 /print:"%t.print" /env:0 /dprint:- "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Color = Red | Green | Blue

method Main() {
  M(Green, Red);
  M(Blue, Blue);
}

// ----- match expressions in general positions

method M(c: Color, d: Color) {
  var x := match c
    case Red => 5
    case Green => 7
    case Blue => 11;
  var y := match c
    case Red => 0.3
    case Green => (match d case Red => 0.18 case Green => 0.21 case Blue => 0.98)
    case Blue => 98.0;
  var z := match c
    case Red => Green
    case Green => match d {
      case Red => Red
      case Green => Blue
      case Blue => Red
    }
    case Blue => Green;
  var w := match c { case Red => 2 case Green => 3 case Blue => 4 } + 10;
  var t := match c
    case Red => 0
    case Green => (match d {
      case Red => 2
      case Green => 2
      case Blue => 1
    } + (((match d case Red => 10 case Green => 8 case Blue => 5))))
    case Blue => (match d {
      case Red => 20
      case Green => 20
      case Blue => 10
    } + (((match d case Red => 110 case Green => 108 case Blue => 105))));
  print x, " ", y, " ", z, " ", w, " ", t, "\n";
}

// ----- match expressions in top-level positions

function Heat(c: Color): int
{
  match c
  case Red => 10
  case Green => 12
  case Blue => 14
}

function IceCream(c: Color): int
{
  match c {
    case Red => 0
    case Green => 4
    case Blue => 1
  }
}

function Flowers(c: Color, d: Color): int
{
  match c {
    case Red =>
      match d {
        case Red => 0
        case Green => 1
        case Blue => 2
      }
    case Green =>
      match d {
        case Red => 3
        case Green => 3
        case Blue => 2
      } + 20
    case Blue =>
      match d {
        case Red => 9
        case Green => 8
        case Blue => 7
      } +
      ((match d case Red => 23 case Green => 29 case Blue => 31))
  }
}

// ----- match statements

method P(c: Color, d: Color) {
  var x: int;
  match c {
    case Red =>
      x := 20;
    case Green =>
    case Blue =>
  }
  match c
  case Red =>
    match d {
      case Red =>
      case Green =>
      case Blue =>
    }
  case Green =>
    var y := 25;
    var z := y + 3;
  case Blue =>
    {
      var y := 25;
      var z := y + 3;
    }
    match d // note: this 'match' is part of the previous case
    case Red =>
    case Green =>
      x := x + 1;
    case Blue =>
}

lemma HeatIsEven(c: Color)
  ensures Heat(c) % 2 == 0;
{
  match c
  case Red =>
    assert 10 % 2 == 0;
  case Green =>
    assert 12 % 2 == 0;
  case Blue =>            // all looks nice, huh? :)
    // obvious
}

method DegenerateExamples(c: Color)
  requires Heat(c) == 10;  // this implies c == Red
{
  match c
  case Red =>
  case Green =>
    match c { }
  case Blue =>
    match c
}

method MoreDegenerateExamples(c: Color)
  requires Heat(c) == 10;  // this implies c == Red
{
  if c == Green {
    var x: int := match c;
    var y: int := match c {};
    var z := match c case Blue => 4;
  }
}
