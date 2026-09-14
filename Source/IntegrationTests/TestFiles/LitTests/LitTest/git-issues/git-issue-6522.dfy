// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets:false --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets:false --type-system-refresh=true --general-newtypes=true "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// An extreme predicate may not quantify over a type whose values can contain an ORDINAL,
// because that lets the predicate branch over a proper class and the prefix-predicate axioms
// assume the stage sequence closes at some ORDINAL. Before the fix for issues 6522 and 6523,
// the check looked only at the bound variable's type and its type arguments, so an ORDINAL
// reachable through a datatype field slipped through and "ensures 1 == 2" could be proved.

datatype S = N(o: ORDINAL) | Top

greatest predicate GreatestViaField(s: S) {
  exists t: S :: t.N? && (s.Top? || t.o < s.o) && GreatestViaField(t)
}

least predicate LeastViaField(s: S) {
  forall t: S :: (t.N? && (s.Top? || t.o < s.o)) ==> LeastViaField(t)
}

// The ORDINAL may be nested arbitrarily deep behind other datatypes ...
datatype Wrapper = Wrap(s: S)

greatest predicate ViaNestedDatatype(w: Wrapper) {
  exists v: Wrapper :: v.s.N? && ViaNestedDatatype(v)
}

// ... and the datatype may be recursive, which the walk must not loop on.
datatype Rec = Nil | Cons(o: ORDINAL, next: Rec)

greatest predicate ViaRecursiveDatatype(r: Rec) {
  exists q: Rec :: q.Cons? && ViaRecursiveDatatype(q)
}

// Codatatype fields are the same story.
codatatype Stream = More(o: ORDINAL, tail: Stream)

greatest predicate ViaCodatatype(c: Stream) {
  exists d: Stream :: d.o < c.o && ViaCodatatype(d)
}

// A type synonym or subset type in between does not hide the ORDINAL either.
type Synonym = S
type Subset = s: S | true witness Top

greatest predicate ViaSynonym(a: Synonym) {
  exists x: Synonym :: x.N? && ViaSynonym(x)
}

greatest predicate ViaSubsetType(b: Subset) {
  exists y: Subset :: y.N? && ViaSubsetType(y)
}

// An "iset" comprehension has no finiteness requirement, so it too can range over a proper class.
greatest predicate ViaInfiniteSetComprehension(s: S) {
  (iset y: S | y.N?) != iset{} && ViaInfiniteSetComprehension(s)
}

// Reaching the ORDINAL through an arrow type counts as well: the functions from a proper class are
// themselves a proper class.
greatest predicate ViaArrowType(s: S) {
  exists f: S -> bool :: f(s) && ViaArrowType(s)
}

// Collections of such a datatype remain legal, both as type arguments and as the type of a
// bound variable outside an extreme predicate. Only quantifying inside one is restricted.
const someSet: set<S> := {Top}
const someSeq: seq<S> := [Top]

method UsesMap(m: map<S, int>) returns (b: bool) {
  b := forall t: S :: t in m.Keys ==> m[t] == 0;
}

// Quantifying over the datatype is also still fine in an ordinary predicate.
ghost predicate OrdinaryPredicate(s: S) {
  exists t: S :: t.N? && t.o < 3
}

// Types whose definition is not visible here are handled in git-issue-6522-opaque-types.dfy: they
// cannot be checked in this file, because that check runs during bounds discovery, a pass that is
// skipped once a file has resolution errors.
