// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets:false --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets:false --type-system-refresh=true --general-newtypes=true "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// The rejected predicates recurse under an existential (greatest) or universal (least) quantifier
// whose variable may range over as many values as there are ordinals.

datatype S = N(o: ORDINAL) | Top

// Issue 6522
greatest predicate GreatestExists(s: S) {
  exists t: S :: t.N? && (s.Top? || t.o < s.o) && GreatestExists(t)
}

// Issue 6523
least predicate LeastForall(s: S) {
  forall t: S :: (t.N? && (s.Top? || t.o < s.o)) ==> LeastForall(t)
}

// The recursive call in the range
greatest predicate CallInTheRange(s: S) {
  exists t: S | CallInTheRange(t) :: t.N?
}

// The ORDINAL behind a type argument, another datatype, a recursive datatype, a codatatype, a synonym,
// a subset type
greatest predicate ViaTypeArgument(p: (S, int)) {
  exists q: (S, int) :: q.0.N? && ViaTypeArgument(q)
}

datatype Wrapper = Wrap(s: S)

greatest predicate ViaNestedDatatype(w: Wrapper) {
  exists v: Wrapper :: v.s.N? && ViaNestedDatatype(v)
}

datatype Rec = Nil | Cons(o: ORDINAL, next: Rec)

greatest predicate ViaRecursiveDatatype(r: Rec) {
  exists q: Rec :: q.Cons? && ViaRecursiveDatatype(q)
}

codatatype Stream = More(o: ORDINAL, tail: Stream)

greatest predicate ViaCodatatype(c: Stream) {
  exists d: Stream :: d.o < c.o && ViaCodatatype(d)
}

type Synonym = S
type Subset = s: S | true witness Top

greatest predicate ViaSynonym(a: Synonym) {
  exists x: Synonym :: x.N? && ViaSynonym(x)
}

greatest predicate ViaSubsetType(b: Subset) {
  exists y: Subset :: y.N? && ViaSubsetType(y)
}

// Types that may stand for S
greatest predicate ViaTypeParameter<T(!new)>(lt: (T, T) -> bool, s: T) {
  exists t: T :: lt(t, s) && ViaTypeParameter(lt, t)
}

type Abstract(==)

greatest predicate ViaAbstractType(p: Abstract -> bool, s: Abstract) {
  exists t: Abstract :: p(t) && ViaAbstractType(p, t)
}

trait Trait {}

greatest predicate ViaTrait(xs: iset<Trait>, s: Trait) {
  exists t :: t in xs && ViaTrait(xs, t)
}

module Exporter {
  export provides Hidden
  datatype S = N(o: ORDINAL) | Top
  type Hidden(!new) = S
}

greatest predicate ViaHiddenType(h: Exporter.Hidden) {
  exists i: Exporter.Hidden :: ViaHiddenType(i)
}

// An iset may hold every value of S
greatest predicate ViaISet(xs: iset<S>, s: S) {
  exists t :: t in xs && ViaISet(xs, t)
}

greatest predicate ViaSubsetsOfAnISet(xs: iset<S>, s: iset<S>) {
  exists x: iset<S> :: x <= xs && ViaSubsetsOfAnISet(xs, x)
}

// Legal: the other two combinations of predicate and quantifier
greatest predicate GreatestForall(s: S) {
  forall t: S :: (t.N? && (s.Top? || t.o < s.o)) ==> GreatestForall(t)
}

least predicate LeastExists(s: S) {
  exists t: S :: t.N? && (s.Top? || t.o < s.o) && LeastExists(t)
}

// Legal: a reference type, whose values are references
trait ReferenceTrait extends object {}

greatest predicate OverAReferenceTrait(xs: iset<ReferenceTrait>, s: ReferenceTrait) {
  exists t :: t in xs && OverAReferenceTrait(xs, t)
}

// Legal: a generic datatype whose type arguments do not involve ORDINAL
greatest predicate GenericDatatypeOfSmallTypes(p: (int, int)) {
  exists q: (int, int) :: q.0 < p.0 && GenericDatatypeOfSmallTypes(q)
}

// Legal: a finite range, of any type
greatest predicate BoundedOverAbstractType(m: map<Abstract, int>, n: map<Abstract, int>) {
  exists y :: y in m && y in n && BoundedOverAbstractType(m, n)
}

// Legal: the variable that may involve ORDINAL is bounded, and the unbounded one does not
greatest predicate BoundedAlongsideAnUnboundedNat(xs: set<S>, s: S) {
  exists t, n: nat :: t in xs && n > 0 && BoundedAlongsideAnUnboundedNat(xs, t)
}

// Legal: the quantifier does not contain the recursive call
greatest predicate QuantifierWithoutTheCall(s: S) {
  (exists t: S :: t.N?) && QuantifierWithoutTheCall(s)
}

// A recursive call in a comprehension gets the error that does not mention ORDINAL
greatest predicate ViaISetComprehension(s: S) {
  (iset t: S | t.N? && ViaISetComprehension(t)) != iset{}
}
