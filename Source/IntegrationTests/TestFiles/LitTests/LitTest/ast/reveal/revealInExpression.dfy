// RUN: echo 'turned off for the moment'
// NOOP: ! %verify --type-system-refresh --allow-axioms --isolate-assertions %s > %t
// NOOP: %diff "%s.expect" "%t"

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
  assert P(1); // error
  var b := (var x := (reveal P; assert P(2); true); 
            assert P(3); x); // error
  var c := (var x: bool :| (reveal P; assert P(4); x); 
            assert P(5); x); // error
  var d := (forall x: int :: reveal P; assert P(x); Q(x)) || 
           (assert P(7); true); // error
  var e := ((x: bool) => reveal P; assert P(7); x)(true) || 
           (assert P(8); true); // error
}

function MatchExpressionScope(x: int): int {
  hide *;
  var x := match x {
    case 0 =>
      reveal P; assert P(0); 1
    case _ =>
      assert P(0); 2 // error
  };
  assert P(1); // error
  x
}