// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The point of all of these tests is to make sure no boolean operators slip into
// the triggers passed to Boogie (which would cause Dafny to crash).
// The verifier is unable to prove many of these assertions, but that's not the point
// of these tests, so I won't bother marking them as errors.

lemma Sets<T>() {
  assert forall a: set<T>, b: set<T> :: a <= b;
  assert forall a: set<T>, b: set<T> :: a < b; // trigger: a <= b
  assert forall a: set<T>, b: set<T> :: a > b; // trigger: a >= b (which is eventually represented as b <= a)
  assert forall a: set<T>, b: set<T> :: a >= b;
  assert forall a: set<T>, b: set<T> :: a + b == b;
  assert forall a: set<T>, b: set<T> :: a - b == b;
  assert forall a: set<T>, b: set<T> :: a * b == b;
  assert forall a: set<T>, b: set<T> :: a !! b; // no trigger
  assert forall a: set<T>, t: T :: t in a;
}

lemma ISets<T>() {
  assert forall a: iset<T>, b: iset<T> :: a <= b;
  assert forall a: iset<T>, b: iset<T> :: a < b; // trigger: a <= b
  assert forall a: iset<T>, b: iset<T> :: a > b; // trigger: a >= b (which is eventually represented as b <= a)
  assert forall a: iset<T>, b: iset<T> :: a >= b;
  assert forall a: iset<T>, b: iset<T> :: a + b == b;
  assert forall a: iset<T>, b: iset<T> :: a - b == b;
  assert forall a: iset<T>, b: iset<T> :: a * b == b;
  assert forall a: iset<T>, b: iset<T> :: a !! b; // no trigger
  assert forall a: iset<T>, t: T :: t in a;
}

lemma Multisets<T>() {
  assert forall a: multiset<T>, b: multiset<T> :: a <= b;
  assert forall a: multiset<T>, b: multiset<T> :: a < b; // trigger: a <= b
  assert forall a: multiset<T>, b: multiset<T> :: a > b; // trigger: a >= b (which is eventually represented as b <= a)
  assert forall a: multiset<T>, b: multiset<T> :: a >= b;
  assert forall a: multiset<T>, b: multiset<T> :: a + b == b;
  assert forall a: multiset<T>, b: multiset<T> :: a - b == b;
  assert forall a: multiset<T>, b: multiset<T> :: a * b == b;
  assert forall a: multiset<T>, b: multiset<T> :: a !! b; // no trigger
  assert forall a: multiset<T>, b: multiset<T>, t: T :: a[t] == b[t];
  assert forall a: multiset<T>, t: T :: t in a;
}

lemma Sequences<T>() {
  assert forall a: seq<T>, b: seq<T> :: a <= b; // no trigger
  assert forall a: seq<T>, b: seq<T> :: a < b; // no trigger
  assert forall a: seq<T>, b: seq<T> :: a + b == b;
  assert forall a: seq<T>, b: seq<T>, t: nat :: a[t] == b[t];
  assert forall a: seq<T>, t: T :: t in a;
}
