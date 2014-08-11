
datatype List<A> = Nil | Cons(hd: A,tl: List<A>);

function method Map<A,B>(f : A -> B, xs : List<A>) : List<B>
  requires forall x :: f.requires(x);
  reads *;
  decreases xs;
{
  match xs
    case Nil => Nil
    case Cons(x,xs) => Cons(f(x),Map(f,xs))
}

function method Id<A>(x : A) : A { x }

method Test() {
  assert Map(Id, Cons(1,Nil)) == Cons(1,Nil);
  var inc := x => x + 1;
  assert Map(inc, Cons(1,Nil)) == Cons(2,Nil);
  assert Map(x => x + 1, Cons(1,Nil)) == Cons(2,Nil);
  assert Map((x) requires x > 0 => x + 1, Nil) == Nil;
}

function CanCall<A,B>(f : A -> B, xs : List<A>) : bool
  decreases xs;
  reads *;
{
  match xs
    case Nil => true
    case Cons(x,xs) => f.requires(x) && CanCall(f, xs)
}

function method MegaMap<A,B>(f : A -> B, xs : List<A>) : List<B>
  requires CanCall(f, xs);
  reads *;
  decreases xs;
{
  match xs
    case Nil => Nil
    case Cons(x,xs) => Cons(f(x),MegaMap(f,xs))
}

method Test2() {
  assert MegaMap((x) requires x != 0 => 100 / x, Cons(2, Nil)).hd == 50;
}

function All<A>(p : A -> bool, xs : List<A>) : bool
  requires forall x :: p.requires(x) /* && p.reads(x) == {} */;
  reads *;
  decreases xs;
{
  match xs
    case Nil => true
    case Cons(x,xs) => p(x) && All(p,xs)
}

/*
function UnionMap(i : A -> set<B>, ys : List<A>): set<B>
  requires forall x :: i.requires(x) && i.reads(x) == {};
  decreases ys;
{
  match ys
    case Nil => {}
    case Cons(x,xs) => i(x) + UnionMap(i,xs)
}
*/

function method NinjaMap<A,B>(f : A -> B, ys : List<A>) : List<B>
  requires All(f.requires, ys);
//  reads UnionMap(f.reads, ys);
  reads *;
  decreases ys;
{
  match ys
    case Nil => Nil
    case Cons(x,xs) => Cons(f(x),NinjaMap(f,xs))
}

function method Compose(f : B -> C, g : A -> B) : A -> C
{
  x requires g.requires(x) && f.requires(g(x))
    reads    g.reads(x) + f.reads(g(x))
    => f(g(x))
}

lemma {:induction 0} MapCompose(f : B -> C, g : A -> B, xs : List<A>)
  requires All(g.requires, xs);
  requires All(f.requires, NinjaMap(g,xs));
  requires All(Compose(f,g).requires, xs);

  decreases xs;
  ensures NinjaMap(f,NinjaMap(g,xs)) == NinjaMap(Compose(f,g),xs);
{
  match xs
    case Nil =>
    case Cons(x,xs) =>
      calc {
            NinjaMap(f,NinjaMap(g,Cons(x,xs)));
         == NinjaMap(f,Cons(g(x),NinjaMap(g,xs)));
         == Cons(f(g(x)),NinjaMap(f,NinjaMap(g,xs)));
         == { MapCompose(f,g,xs); }
            Cons(f(g(x)),NinjaMap(Compose(f,g),xs));
         == Cons(Compose(f,g)(x),NinjaMap(Compose(f,g),xs));
         == NinjaMap(Compose(f,g),Cons(x,xs));
      }
}

// auto-mode
lemma MapCompose2(f : B -> C, g : A -> B, xs : List<A>)
  requires All(g.requires, xs);
  requires All(f.requires, NinjaMap(g,xs));
  requires All(Compose(f,g).requires, xs);
  decreases xs;
  ensures NinjaMap(f,NinjaMap(g,xs)) == NinjaMap(Compose(f,g),xs);
{
}

