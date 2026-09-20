// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets:false --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets:false --type-system-refresh=true --general-newtypes=true "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// An extreme predicate indexed by ORDINAL relies on its sequence of approximations closing at some
// ORDINAL, which requires the states reachable by unfolding the definition to form a set. A type
// with an ORDINAL in it has as many values as there are ordinals, so enumerating one under the
// quantifier direction that does not distribute over the limits of that sequence -- an existential
// for a greatest predicate, a universal for a least one -- leaves the fixpoint indexed by no
// ORDINAL at all. Before the fix for issues 6522 and 6523, each of the rejected declarations below
// could be used to prove "1 == 2".

datatype S = N(o: ORDINAL) | Top

// Issue 6522: greatest predicate, existential.
greatest predicate GreatestExists(s: S) {
  exists t: S :: t.N? && (s.Top? || t.o < s.o) && GreatestExists(t)
}

// Issue 6523: least predicate, universal. The exact dual.
least predicate LeastForall(s: S) {
  forall t: S :: (t.N? && (s.Top? || t.o < s.o)) ==> LeastForall(t)
}

// The ORDINAL may be nested arbitrarily deep behind other datatypes ...
datatype Wrapper = Wrap(s: S)

greatest predicate ViaNestedDatatype(w: Wrapper) {
  exists v: Wrapper :: v.s.N? && ViaNestedDatatype(v)
}

// ... the datatype may be recursive, which the walk must not loop on ...
datatype Rec = Nil | Cons(o: ORDINAL, next: Rec)

greatest predicate ViaRecursiveDatatype(r: Rec) {
  exists q: Rec :: q.Cons? && ViaRecursiveDatatype(q)
}

// ... codatatype fields are the same story ...
codatatype Stream = More(o: ORDINAL, tail: Stream)

greatest predicate ViaCodatatype(c: Stream) {
  exists d: Stream :: d.o < c.o && ViaCodatatype(d)
}

// ... and a type synonym or subset type in between does not hide it either.
type Synonym = S
type Subset = s: S | true witness Top

greatest predicate ViaSynonym(a: Synonym) {
  exists x: Synonym :: x.N? && ViaSynonym(x)
}

greatest predicate ViaSubsetType(b: Subset) {
  exists y: Subset :: y.N? && ViaSubsetType(y)
}

// A type parameter or an abstract type could stand for such a type, so enumerating the whole of one
// is rejected as well. (Without this, the same proof of "1 == 2" goes through with the quantifier
// reading 'exists t: T', which no type-based check on the bound variable would catch.)
greatest predicate ViaTypeParameter<T(!new)>(lt: (T, T) -> bool, s: T) {
  exists t: T :: lt(t, s) && ViaTypeParameter(lt, t)
}

type Abstract(==)

greatest predicate ViaAbstractType(p: Abstract -> bool, s: Abstract) {
  exists t: Abstract :: p(t) && ViaAbstractType(p, t)
}

// The other two cells of the square are sound, and stay legal: a universal distributes over the
// decreasing limits of a greatest predicate's approximations, and an existential over the
// increasing limits of a least predicate's, so those close at omega however large the type is.
greatest predicate GreatestForall(s: S) {
  forall t: S :: (t.N? && (s.Top? || t.o < s.o)) ==> GreatestForall(t)
}

least predicate LeastExists(s: S) {
  exists t: S :: t.N? && (s.Top? || t.o < s.o) && LeastExists(t)
}

// Confining the bound variable to a finite range also keeps the branching set-sized, whatever the
// type is. (This is the shape used by dafny4/KozenSilva.dfy, where "Var" is uninterpreted and the
// quantifier is bounded by the domain of a finite map.)
greatest predicate BoundedOverAbstractType(m: map<Abstract, int>, n: map<Abstract, int>) {
  exists y :: y in m && y in n && BoundedOverAbstractType(m, n)
}

// And a quantifier that does not contain the recursive call cannot affect the fixpoint at all.
greatest predicate QuantifierWithoutTheCall(s: S) {
  (exists t: S :: t.N?) && QuantifierWithoutTheCall(s)
}

// It has to be one and the same variable that is unbounded and of such a type. Here 't' is the one
// whose type may involve ORDINAL and it is confined to a finite set, while the unbounded 'n' ranges
// over a type that has only set-many values, so the reachable states still form a set.
greatest predicate BoundedAlongsideAnUnboundedNat(xs: set<S>, s: S) {
  exists t, n: nat :: t in xs && n > 0 && BoundedAlongsideAnUnboundedNat(xs, t)
}

// An iset holds set-many elements even though it is infinite, so ranging over the elements of one
// keeps the states a set as well. (Outright finiteness is what the nat-indexed case needs, not this.)
greatest predicate BoundedByAnISet(xs: iset<S>, s: S) {
  exists t :: t in xs && BoundedByAnISet(xs, t)
}

// Likewise the subsets of a collection, which form a power set.
greatest predicate BoundedBySubsetsOfAnISet(xs: iset<S>, s: iset<S>) {
  exists x: iset<S> :: x <= xs && BoundedBySubsetsOfAnISet(xs, x)
}

// A recursive call inside a comprehension is already rejected, by the pre-existing rule that such a
// call must be in a positive position, so the ORDINAL rule never has to consider one.
greatest predicate ViaISetComprehension(s: S) {
  (iset t: S | t.N? && ViaISetComprehension(t)) != iset{}
}

// Collections of such a datatype remain legal everywhere, as does quantifying over it outside an
// extreme predicate.
const someSet: set<S> := {Top}
const someSeq: seq<S> := [Top]

ghost predicate OrdinaryPredicate(s: S) {
  exists t: S :: t.N? && t.o < 3
}
