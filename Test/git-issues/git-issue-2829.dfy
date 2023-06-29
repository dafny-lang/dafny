// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Either<+L, +R> = Left(l: L) | Right(r: R)

datatype Lang<!A> = Lang(mem: (string, A) -> bool, repr: iset<A>)

ghost function Atom<A>(s: string, value: A): Lang<A> {
  Lang((input, a) => s == input && a == value, iset{})
}

ghost function Char(c: char): Lang<char> {
  Atom([c], c)
}

ghost function EitherL<A, B>(l: Lang<A>, r: Lang<B>): Lang<Either<A, B>> {
  Lang((input, ab: Either<A, B>) =>
    || (exists a | a in l.repr :: ab == Left(a) && l.mem(input, a))
    || (exists b | b in r.repr :: ab == Right(b) && r.mem(input, b)),
    (iset a | a in l.repr :: Left(a)) + (iset b | b in r.repr :: Right(b))
  )
}

// Nondeterministic in general
ghost function ConcatL<A, B> (l: Lang<A>, r: Lang<B>): Lang<(A, B)> {
  Lang((input, p) =>
    exists s1, s2, a, b | a in l.repr && b in r.repr::
      input == s1 + s2 && p == (a, b),
    iset a, b | a in l.repr && b in r.repr :: (a,b)
  )
}

ghost function Empty<A>(): Lang<A> { Lang((_, _) => false, iset{}) }

ghost function MapL<A, B> (l: Lang<A>, f: A -> B): Lang<B> {
  Lang((input, b) =>
    exists a: A | a in l.repr :: b == f(a) && l.mem(input, a),
    iset a | a in l.repr :: f(a)
  )
}

ghost function Ignore<A>(l: Lang<A>): Lang<()> { MapL(l, (_) => ()) }

ghost function Epsilon(): Lang<()> {
  Lang((input, _) => input == "", iset{})
}

ghost function RepeatAux<A>(pred : (string, A) -> bool, repr: iset<A>, input: string, output: seq<A>): bool
  decreases |output|
{
  || (input == "" && output == [])
  || (exists init, tail, a, alist | a in repr ::
      && input == init + tail
      && output == [a] + alist
      && pred(a, init)
      && RepeatAux(pred, repr, tail, alist))
}
