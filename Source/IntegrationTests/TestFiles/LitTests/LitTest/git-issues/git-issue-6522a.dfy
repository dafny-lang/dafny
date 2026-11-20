// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A newtype has as many values as its base type

datatype S = N(o: ORDINAL) | Top

newtype SetOfS = set<S>

greatest predicate ViaNewtype(s: SetOfS) {
  exists t: SetOfS :: |(t as set<S>)| == 1 && ViaNewtype(t)
}

// Legal
newtype SetOfInt = set<int>

greatest predicate NewtypeWithoutOrdinal(s: SetOfInt) {
  exists t: SetOfInt :: |(t as set<int>)| == 1 && NewtypeWithoutOrdinal(t)
}
