// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<A> = None | Some(get: A) {
  function method Bind<B>(f: A -> Option<B>): Option<B> {
    if this == None then None else f(get)
  }
}

// -------------------------------

datatype List<A> = Nil | Cons(head: A, tail: List<A>)

function method Head(list: List): Option {
  if list == Nil then None else Some(list.head)
}
function method Tail(list: List): Option<List> {
  if list == Nil then None else Some(list.tail)
}

// -------------------------------

// F, G, and H return element 2 of list, if any
function method F(list: List): Option {
  match list
  case Nil => None
  case Cons(_, cdr) =>
    match cdr
    case Nil => None
    case Cons(_, cddr) =>
      match cddr
      case Nil => None
      case Cons(x, _) => Some(x)
}

function method G(list: List): Option {
  Tail(list).Bind(cdr =>
  Tail(cdr).Bind(cddr =>
  Head(cddr)))
}

/* The following uses :- */
function method H(list: List): Option {
  var cdr :- Tail(list);
   var cddr :- Tail(cdr);
  Head(cddr)
}


lemma FG(list: List)
  ensures F(list) == G(list)
{}


lemma FGH(list: List)
  ensures F(list) == G(list) == H(list)
{}


lemma Examples() {
  var aa := Cons(5, Cons(6, Nil));
  var bb := Cons(4, aa);
  assert F(aa) == None && F(bb) == Some(6);
  assert G(aa) == None && G(bb) == Some(6);
  assert H(aa) == None && H(bb) == Some(6);
}
