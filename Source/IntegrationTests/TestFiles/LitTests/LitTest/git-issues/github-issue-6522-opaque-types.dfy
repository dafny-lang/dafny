// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets:false --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename --show-snippets:false --type-system-refresh=true --general-newtypes=true "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Companion to github-issue-6522.dfy, for the types whose definition is not visible at the
// extreme predicate -- a type parameter or an abstract type. Such a type could be instantiated
// with one that involves an ORDINAL (for instance the "datatype S = N(o: ORDINAL) | Top" of
// issues 6522 and 6523), which would let the extreme predicate branch over a proper class.
//
// These cases live in their own file because they are reported during bounds discovery, and that
// pass is skipped once a file already has resolution errors.

// Ranging over the whole type is rejected ...

greatest predicate UnboundedOverTypeParameter<T(!new)>(lt: (T, T) -> bool, s: T) {
  exists t: T :: lt(t, s) && UnboundedOverTypeParameter(lt, t)
}

type Abstract(==)

greatest predicate UnboundedOverAbstractType(p: Abstract -> bool, s: Abstract) {
  exists t: Abstract :: p(t) && UnboundedOverAbstractType(p, t)
}

least predicate UnboundedLeastOverTypeParameter<T(!new)>(lt: (T, T) -> bool, s: T) {
  forall t: T :: lt(t, s) ==> UnboundedLeastOverTypeParameter(lt, t)
}

// ... but only when the bound variable really does range over the whole type. Confined to a
// finite range, the branching is set-sized whatever the type turns out to be, so these are legal.
// (This is the shape used by dafny4/KozenSilva.dfy, where "Var" is an uninterpreted type and the
// quantifier is bounded by the domain of a finite map.)

greatest predicate BoundedOverAbstractType(m: map<Abstract, int>, n: map<Abstract, int>) {
  forall y :: y in m ==> y in n && BoundedOverAbstractType(m, n)
}

greatest predicate BoundedOverTypeParameter<T(!new, ==)>(xs: set<T>, f: set<T> -> bool) {
  forall y :: y in xs ==> f(xs) && BoundedOverTypeParameter(xs, f)
}

// The same holds for a datatype whose definition is hidden by an export set: it might involve an
// ORDINAL, but a bound variable confined to a finite range cannot branch over a proper class.
module Library {
  export provides Hidden
  datatype Hidden = H(o: ORDINAL) | Sentinel
}

module Client {
  import Library

  greatest predicate BoundedOverHiddenDatatype(m: map<Library.Hidden, int>, n: map<Library.Hidden, int>) {
    forall y :: y in m ==> y in n && BoundedOverHiddenDatatype(m, n)
  }
}
