// RUN: %exits-with 4 %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NoAutoInit {
  trait GeneralTrait { }
  trait ReferenceTrait extends object { }

  datatype A = A(g: GeneralTrait)
  datatype B = B(h: ReferenceTrait)

  method Test() {
    var a: A := *;
    var b: B := *;

    if * {
      print a, "\n"; // error: A is a possibly empty type, so "a" is subject to definite assignment
    } else {
      print b, "\n"; // error: B is a possibly empty type, so "b" is subject to definite assignment
    }
  }
}
