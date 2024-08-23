// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


datatype T = A(int) | B(nat) | C(bool)

method Variables(t: T) {
  match t
    case A(n) // Error: Or-patterns may not bind variables
       | B(n) => // Error: Or-patterns may not bind variables AND Error: duplicate name
    case _ =>
}

method Nesting(t: T) {
  match t
    case A(1 | 2 | _) => // Error: Or-patterns are not allowed inside other patterns
    case B(0 | _) // Error: Or-patterns are not allowed inside other patterns
       | C(_ | _ | _) => // Error: Or-patterns are not allowed inside other patterns
}
