// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<A> = None | Some(get: A) {
  function method Bind<B>(f: A --> Option<B>): Option<B>
    requires this == None || f.requires(this.get)
    reads if this == None then {} else f.reads(this.get)
  {
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

class Cell {
  var data: int
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

/* The following uses :- with a requires clause */
function method I(list: List): Option {
  var cdr requires list != Nil :- Tail(list);
  Head(cdr)
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

method Main() {
  var zz := Cons(6, Nil);
  var aa := Cons(5, zz);
  var bb := Cons(4, aa);
  print "Third element of [4::5::6] is:", H(bb), " is the second element of [5::6]:", I(aa), "?", if H(bb) == I(aa) then " yes" else " no","\n";
  print "The second element of [6] is:", I(zz), "?", if I(zz) == None then " yes" else " no","\n";
}