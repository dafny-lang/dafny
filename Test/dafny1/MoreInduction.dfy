// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<X> = Nil | Cons(Node<X>, List<X>);
datatype Node<X> = Element(X) | Nary(List<X>);

function FlattenMain<X>(list: List<X>): List<X>
  ensures IsFlat(FlattenMain(list));
{
  Flatten(list, Nil)
}

function Flatten<X>(list: List<X>, ext: List<X>): List<X>
  requires IsFlat(ext);
  ensures IsFlat(Flatten(list, ext));
{
  match list
  case Nil => ext
  case Cons(n, rest) =>
    match n
    case Element(x) => Cons(n, Flatten(rest, ext))
    case Nary(nn) => Flatten(nn, Flatten(rest, ext))
}

function IsFlat<X>(list: List<X>): bool
{
  match list
  case Nil => true
  case Cons(n, rest) =>
    match n
    case Element(x) => IsFlat(rest)
    case Nary(nn) => false
}

function ToSeq<X>(list: List<X>): seq<X>
{
  match list
  case Nil => []
  case Cons(n, rest) =>
    match n
    case Element(x) => [x] + ToSeq(rest)
    case Nary(nn) => ToSeq(nn) + ToSeq(rest)
}

ghost method Theorem<X>(list: List<X>)
  ensures ToSeq(list) == ToSeq(FlattenMain(list));
{
  Lemma(list, Nil);
}

ghost method Lemma<X>(list: List<X>, ext: List<X>)
  requires IsFlat(ext);
  ensures ToSeq(list) + ToSeq(ext) == ToSeq(Flatten(list, ext));
{
  match (list) {
    case Nil =>
    case Cons(n, rest) =>
      match (n) {
        case Element(x) =>
          Lemma(rest, ext);
        case Nary(nn) =>
          Lemma(nn, Flatten(rest, ext));
          Lemma(rest, ext);
      }
  }
}

// ---------------------------------------------

function NegFac(n: int): int
  decreases -n;
{
  if -1 <= n then -1 else - NegFac(n+1) * n
}

ghost method LemmaAll()
  ensures forall n :: NegFac(n) <= -1;  // error: induction heuristic does not give a useful well-founded order, and thus this fails to verify
{
}

ghost method LemmaOne(n: int)
  ensures NegFac(n) <= -1;  // error: induction heuristic does not give a useful well-founded order, and thus this fails to verify
{
}

ghost method LemmaAll_Neg()
  ensures forall n :: NegFac(-n) <= -1;  // error: fails to verify because of the minus in the trigger
{
}

ghost method LemmaOne_Neg(n: int)
  ensures NegFac(-n) <= -1;  // error: fails to verify because of the minus in the trigger
{
}

ghost method LemmaOneWithDecreases(n: int)
  ensures NegFac(n) <= -1;  // here, the programmer gives a good well-founded order, so this verifies
  decreases -n;
{
}
