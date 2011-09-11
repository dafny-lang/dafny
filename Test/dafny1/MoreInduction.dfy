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
