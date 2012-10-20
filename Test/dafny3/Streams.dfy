// ----- Stream

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream);

function append(M: Stream, N: Stream): Stream
{
  match M
  case Nil => N
  case Cons(t, M') => Cons(t, append(M', N))
}

// ----- f, g, and maps

type X;

function f(x: X): X
function g(x: X): X

function map_f(M: Stream<X>): Stream<X>
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(f(x), map_f(N))
}

function map_g(M: Stream<X>): Stream<X>
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(g(x), map_g(N))
}

function map_fg(M: Stream<X>): Stream<X>
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(f(g(x)), map_fg(N))
}

// ----- Theorems

// map (f * g) M = map f (map g M)
comethod Theorem0(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{
  match (M) {
    case Nil =>
    case Cons(x, N) =>
      Theorem0(N);
  }
}
comethod Theorem0_alt(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{
  if (M.Cons?) {
    Theorem0(M.tail);
  }
}

// map f (append M N) = append (map f M) (map f N)
comethod Theorem1(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  match (M) {
    case Nil =>
    case Cons(x, M') =>
      Theorem1(M', N);
  }
}
comethod Theorem1_alt(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  if (M.Cons?) {
    Theorem1(M.tail, N);
  }
}

// append NIL M = M
ghost method Theorem2(M: Stream<X>)
  ensures append(Nil, M) == M;
{
  // trivial
}

// append M NIL = M
comethod Theorem3(M: Stream<X>)
  ensures append(M, Nil) == M;
{
  match (M) {
    case Nil =>
    case Cons(x, N) =>
      Theorem3(N);
  }
}
comethod Theorem3_alt(M: Stream<X>)
  ensures append(M, Nil) == M;
{
  if (M.Cons?) {
    Theorem3(M.tail);
  }
}

// append M (append N P) = append (append M N) P
comethod Theorem4(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{
  match (M) {
    case Nil =>
    case Cons(x, M') =>
      Theorem4(M', N, P);
  }
}
comethod Theorem4_alt(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{
  if (M.Cons?) {
    Theorem4(M.tail, N, P);
  }
}

// ----- Flatten

// Flatten can't be written as just:
//
//     function SimpleFlatten<T>(M: Stream<Stream>): Stream
//     {
//       match M
//       case Nil => Nil
//       case Cons(s, N) => append(s, SimpleFlatten(N))
//     }
//
// because this function fails to be productive given an infinite stream of Nil's.
// Instead, here are two variations SimpleFlatten.  The first variation (FlattenStartMarker)
// prepends a "startMarker" to each of the streams in "M".  The other (FlattenNonEmpties)
// insists that "M" contains no empty streams.  One can prove a theorem that relates these
// two versions.

// This first variation of Flatten returns a stream of the streams in M, each preceded with
// "startMarker".

function FlattenStartMarker<T>(M: Stream<Stream>, startMarker: T): Stream
{
  FlattenStartMarkerAcc(Nil, M, startMarker)
}

function FlattenStartMarkerAcc<T>(accumulator: Stream, M: Stream<Stream>, startMarker: T): Stream
{
  match accumulator
  case Cons(hd, tl) =>
    Cons(hd, FlattenStartMarkerAcc(tl, M, startMarker))
  case Nil =>
    match M
    case Nil => Nil
    case Cons(s, N) => Cons(startMarker, FlattenStartMarkerAcc(s, N, startMarker))
}

// The next variation of Flatten requires M to contain no empty streams.

copredicate StreamOfNonEmpties(M: Stream<Stream>)
{
  match M
  case Nil => true
  case Cons(s, N) => s.Cons? && StreamOfNonEmpties(N)
}

function FlattenNonEmpties(M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M);
{
  FlattenNonEmptiesAcc(Nil, M)
}

function FlattenNonEmptiesAcc(accumulator: Stream, M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M);
{
  match accumulator
  case Cons(hd, tl) =>
    Cons(hd, FlattenNonEmptiesAcc(tl, M))
  case Nil =>
    match M
    case Nil => Nil
    case Cons(s, N) => Cons(s.head, FlattenNonEmptiesAcc(s.tail, N))
}

// We can prove a theorem that links the previous two variations of flatten.  To
// do that, we first define a function that prepends an element to each stream
// of a given stream of streams.
// The "assume" statements below are temporary workaround.  They make the proofs
// unsound, but, as a temporary measure, they express the intent of the proofs.

function Prepend<T>(x: T, M: Stream<Stream>): Stream<Stream>
  ensures StreamOfNonEmpties(Prepend(x, M));
{
  match M
  case Nil => Nil
  case Cons(s, N) => Cons(Cons(x, s), Prepend(x, N))
}

ghost method Theorem_Flatten<T>(M: Stream<Stream>, startMarker: T)
  ensures FlattenStartMarker(M, startMarker) == FlattenNonEmpties(Prepend(startMarker, M));
{
  Lemma_Flatten(Nil, M, startMarker);
}

comethod Lemma_Flatten<T>(accumulator: Stream, M: Stream<Stream>, startMarker: T)
  ensures FlattenStartMarkerAcc(accumulator, M, startMarker) == FlattenNonEmptiesAcc(accumulator, Prepend(startMarker, M));
{
  calc {
    FlattenStartMarkerAcc(accumulator, M, startMarker);
    { Lemma_FlattenAppend0(accumulator, M, startMarker); }
    append(accumulator, FlattenStartMarkerAcc(Nil, M, startMarker));
    { Lemma_Flatten(Nil, M, startMarker);
      assume FlattenStartMarkerAcc(Nil, M, startMarker) == FlattenNonEmptiesAcc(Nil, Prepend(startMarker, M));  // postcondition of the co-recursive call
    }
    append(accumulator, FlattenNonEmptiesAcc(Nil, Prepend(startMarker, M)));
    { Lemma_FlattenAppend1(accumulator, Prepend(startMarker, M)); }
    FlattenNonEmptiesAcc(accumulator, Prepend(startMarker, M));
  }
}

comethod Lemma_FlattenAppend0<T>(s: Stream, M: Stream<Stream>, startMarker: T)
  ensures FlattenStartMarkerAcc(s, M, startMarker) == append(s, FlattenStartMarkerAcc(Nil, M, startMarker));
{
  match (s) {
    case Nil =>
    case Cons(hd, tl) =>
      calc {
        FlattenStartMarkerAcc(Cons(hd, tl), M, startMarker);
        Cons(hd, FlattenStartMarkerAcc(tl, M, startMarker));
        { Lemma_FlattenAppend0(tl, M, startMarker);
          assume FlattenStartMarkerAcc(tl, M, startMarker) == append(tl, FlattenStartMarkerAcc(Nil, M, startMarker));  // this is the postcondition of the co-recursive call
        }
        Cons(hd, append(tl, FlattenStartMarkerAcc(Nil, M, startMarker)));
        // def. append
        append(Cons(hd, tl), FlattenStartMarkerAcc(Nil, M, startMarker));
      }
  }
}

comethod Lemma_FlattenAppend1<T>(s: Stream, M: Stream<Stream>)
  requires StreamOfNonEmpties(M);
  ensures FlattenNonEmptiesAcc(s, M) == append(s, FlattenNonEmptiesAcc(Nil, M));
{
  match (s) {
    case Nil =>
    case Cons(hd, tl) =>
      calc {
        FlattenNonEmptiesAcc(Cons(hd, tl), M);
        // def. FlattenNonEmptiesAcc
        Cons(hd, FlattenNonEmptiesAcc(tl, M));
        { Lemma_FlattenAppend1(tl, M);
          assume FlattenNonEmptiesAcc(tl, M) == append(tl, FlattenNonEmptiesAcc(Nil, M));  // postcondition of the co-recursive call
        }
        Cons(hd, append(tl, FlattenNonEmptiesAcc(Nil, M)));
        // def. append
        append(Cons(hd, tl), FlattenNonEmptiesAcc(Nil, M));
      }
  }
}
