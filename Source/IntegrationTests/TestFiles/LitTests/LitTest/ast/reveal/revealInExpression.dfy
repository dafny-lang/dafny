// RUN: ! %verify --type-system-refresh --allow-axioms --isolate-assertions %s > %t
// RUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  true
}

function Q(x: int): bool 
  requires P(0) {
  true
}

method RevealExpressionScope()
{
  hide *;
  var a := (reveal P; assert P(0); true);
  assert P(1); // no error, expression leaks.
  var b := (var x := (reveal P; assert P(2); true); 
            assert P(3); x); // no error, expression leaks.
  var c := (var x: bool :| (reveal P; assert P(4); x); 
            assert P(5); x); // no error, expression leaks.
  var d := (forall x: int :: reveal P; assert P(x); Q(x)) || 
           (assert P(7); true); // no error, expression leaks.
  var e := ((x: bool) => reveal P; assert P(7); x)(true) || 
           (assert P(8); true); // no error, expression leaks.
}

function MatchExpressionScope(x: int): int {
  hide *;
  var x := match x {
    case 0 =>
      reveal P; assert P(0); 1
    case _ =>
      assert P(0); 2 // error
  };
  assert P(1); // no error, expression leaks.
  x
}