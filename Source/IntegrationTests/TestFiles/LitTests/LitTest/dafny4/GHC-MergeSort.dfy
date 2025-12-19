// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rustan Leino
// 23 Dec 2013 (completed in 5 hours, but is missing the formulation and proof that the
// sorting algorithm is stable, which the journal article below does and says is the most interesting
// part).
// 28 Dec 2013, added key function and stability (which took another 5 hours).
// Inspiration to prove this algorithm comes from "Proof Pearl --- A Mechanized Proof of GHC's Mergesort"
// by Christian Sternagel, Journal of Automation 51:357--370, 2013.

// library

datatype List<T> = Nil | Cons(head: T, tail: List)

ghost function length(xs: List): nat
{
  match xs
  case Nil => 0
  case Cons(_, ys) => 1 + length(ys)
}

// returns xs-backwards followed-by acc
function reverse(xs: List, acc: List): List
{
  match xs
  case Nil => acc
  case Cons(a, ys) => reverse(ys, Cons(a, acc))
}

ghost function multiset_of<T>(xs: List<T>): multiset<T>
{
  match xs
  case Nil => multiset{}
  case Cons(a, ys) => multiset{a} + multiset_of(ys)
}

ghost function MultisetUnion<T>(xs: List<List<T>>): multiset<T>
{
  match xs
  case Nil => multiset{}
  case Cons(a, ys) => multiset_of(a) + MultisetUnion(ys)
}

ghost function append(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(a, xs') => Cons(a, append(xs', ys))
}

lemma append_associative(xs: List, ys: List, zs: List)
  ensures append(xs, append(ys, zs)) == append(append(xs, ys), zs)
{
}

lemma append_Nil(xs: List)
  ensures append(xs, Nil) == xs
{
}

ghost function flatten(x: List<List>): List
{
  match x
  case Nil => Nil
  case Cons(xs, y) => append(xs, flatten(y))
}

// The algorithm

// Everything is parametric in G and key
type G
function key(g: G): int

predicate Below(a: G, b: G)
{
  key(a) <= key(b)
}

function sort(xs: List<G>): List<G>
{
  mergeAll(sequences(xs))
}

function sequences(xs: List<G>): List<List<G>>
  ensures sequences(xs) != Nil
  decreases xs, 0
{
  match xs
  case Nil => Cons(xs, Nil)
  case Cons(a, ys) =>
    match ys
    case Nil => Cons(xs, Nil)
    case Cons(b, zs) => if !Below(a, b) then descending(b, Cons(a, Nil), zs) else ascending(b, Cons(a, Nil), zs)
}

function descending(a: G, xs: List<G>, ys: List<G>): List<List<G>>
  ensures descending(a, xs, ys) != Nil
  decreases ys
{
  if ys.Cons? && !Below(a, ys.head) then
    descending(ys.head, Cons(a, xs), ys.tail)
  else
    Cons(Cons(a, xs), sequences(ys))
}

function ascending(a: G, xs: List<G>, ys: List<G>): List<List<G>>
  ensures ascending(a, xs, ys) != Nil
  decreases ys
{
  if ys.Cons? && Below(a, ys.head) then
    ascending(ys.head, Cons(a, xs), ys.tail)
  else
    Cons(reverse(Cons(a, xs), Nil), sequences(ys))
}

function mergeAll(x: List<List<G>>): List<G>
  requires x != Nil
  decreases length(x)
{
  if x.tail == Nil then
    x.head
  else
    mergeAll(mergePairs(x))
}

function mergePairs(x: List<List<G>>): List<List<G>>
  ensures length(mergePairs(x)) <= length(x)
  ensures x.Cons? && x.tail.Cons? ==> length(mergePairs(x)) < length(x)
  ensures x != Nil ==> mergePairs(x) != Nil
{
  if x.Cons? && x.tail.Cons? then
    Cons(merge(x.head, x.tail.head), mergePairs(x.tail.tail))
  else
    x
}

function merge(xs: List<G>, ys: List<G>): List<G>
{
  match xs
  case Nil => ys
  case Cons(a, xs') =>
    match ys
    case Nil => xs
    case Cons(b, ys') =>
      if Below(a, b) then Cons(a, merge(xs', ys)) else Cons(b, merge(xs, ys'))
}

lemma MultisetOfMerge(xs: List<G>, ys: List<G>)
  ensures multiset_of(merge(xs, ys)) <= multiset_of(xs) + multiset_of(ys)
{
}

// the specification

ghost predicate sorted(xs: List<G>)
{
  match xs
  case Nil => true
  case Cons(a, ys) =>
    (forall y :: y in multiset_of(ys) ==> Below(a, y)) &&  // using multiset_of instead of set_of, since we don't have a need for set_of elsewhere
    sorted(ys)
}

ghost function filter(g: G, xs: List<G>): List<G>
{
  match xs
  case Nil => Nil
  case Cons(b, ys) => if key(g) == key(b) then Cons(b, filter(g, ys)) else filter(g, ys)
}

ghost predicate stable(xs: List<G>, ys: List<G>)
{
  forall g :: filter(g, xs) == filter(g, ys)  // I dropped the unnecessary antecedent "g in multiset_of(xs)" from the paper
}

lemma Correctness(xs: List<G>)
  ensures sorted(sort(xs)) && multiset_of(sort(xs)) == multiset_of(xs) && stable(sort(xs), xs)
{
  calc {
    multiset_of(sort(xs));
    multiset_of(mergeAll(sequences(xs)));
    { perm_mergeAll(sequences(xs)); }
    MultisetUnion(sequences(xs));
    { perm_sequences(xs); }
    multiset_of(xs);
  }
  sorted_sort(xs);
  forall g {
    stable_sort(g, xs);
  }
}

// permutation lemmas

lemma perm_sequences(xs: List<G>)
  ensures MultisetUnion(sequences(xs)) == multiset_of(xs)
  decreases xs, 0
{
  match xs {
    case Nil =>
    case Cons(a, ys) =>
      match ys {
        case Nil =>
        case Cons(b, zs) =>
          perm_descending(b, Cons(a, Nil), zs);
          perm_ascending(b, Cons(a, Nil), zs);
      }
  }
}

lemma perm_descending(a: G, xs: List<G>, ys: List<G>)
  ensures MultisetUnion(descending(a, xs, ys)) == multiset{a} + multiset_of(xs) + multiset_of(ys)
  decreases ys
{
  if ys.Cons? && !Below(a, ys.head) {
    calc {
      MultisetUnion(descending(a, xs, ys));
      MultisetUnion(descending(ys.head, Cons(a, xs), ys.tail));
      { perm_descending(ys.head, Cons(a, xs), ys.tail); }
      multiset{ys.head} + multiset_of(Cons(a, xs)) + multiset_of(ys.tail);
      multiset{a} + multiset_of(xs) + multiset_of(Cons(ys.head, ys.tail));
    }
  } else {
    calc {
      MultisetUnion(descending(a, xs, ys));
      MultisetUnion(Cons(Cons(a, xs), sequences(ys)));
      multiset_of(Cons(a, xs)) + MultisetUnion(sequences(ys));
      { perm_sequences(ys); }
      multiset_of(Cons(a, xs)) + multiset_of(ys);
      multiset{a} + multiset_of(xs) + multiset_of(ys);
    }
  }
}

lemma perm_ascending(a: G, xs: List<G>, ys: List<G>)
  ensures MultisetUnion(ascending(a, xs, ys)) == multiset{a} + multiset_of(xs) + multiset_of(ys)
  decreases ys
{
  if ys.Cons? && Below(a, ys.head) {
    calc {
      MultisetUnion(ascending(a, xs, ys));
      MultisetUnion(ascending(ys.head, Cons(a, xs), ys.tail));
      { perm_ascending(ys.head, Cons(a, xs), ys.tail); }
      multiset{ys.head} + multiset_of(Cons(a, xs)) + multiset_of(ys.tail);
      multiset{a} + multiset_of(xs) + multiset_of(Cons(ys.head, ys.tail));
    }
  } else {
    calc {
      MultisetUnion(ascending(a, xs, ys));
      MultisetUnion(Cons(reverse(Cons(a, xs), Nil), sequences(ys)));
      multiset_of(reverse(Cons(a, xs), Nil)) + MultisetUnion(sequences(ys));
      { perm_sequences(ys); }
      multiset_of(reverse(Cons(a, xs), Nil)) + multiset_of(ys);
      { perm_reverse(Cons(a, xs), Nil); }
      multiset_of(Cons(a, xs)) + multiset_of(Nil) + multiset_of(ys);
      multiset{a} + multiset_of(xs) + multiset_of(ys);
    }
  }
}

lemma perm_reverse(xs: List, acc: List)
  ensures multiset_of(reverse(xs, acc)) == multiset_of(xs) + multiset_of(acc)
{
}

lemma perm_mergeAll(x: List<List<G>>)
  requires x != Nil
  ensures multiset_of(mergeAll(x)) == MultisetUnion(x)
  decreases length(x)
{
  if x == Nil {
  } else if x.tail == Nil {
  } else {
    calc {
      multiset_of(mergeAll(x));
      multiset_of(mergeAll(mergePairs(x)));
      { perm_mergeAll(mergePairs(x)); }
      MultisetUnion(mergePairs(x));
      { perm_mergePairs(x); }
      MultisetUnion(x);
    }
  }
}

lemma perm_mergePairs(x: List<List<G>>)
  ensures MultisetUnion(mergePairs(x)) == MultisetUnion(x)
{
  if x.Cons? && x.tail.Cons? {
    calc {
      MultisetUnion(mergePairs(x));
      MultisetUnion(Cons(merge(x.head, x.tail.head), mergePairs(x.tail.tail)));
      multiset_of(merge(x.head, x.tail.head)) + MultisetUnion(mergePairs(x.tail.tail));
      { perm_mergePairs(x.tail.tail); }
      multiset_of(merge(x.head, x.tail.head)) + MultisetUnion(x.tail.tail);
      { perm_merge(x.head, x.tail.head); }
      multiset_of(x.head) + multiset_of(x.tail.head) + MultisetUnion(x.tail.tail);
      multiset_of(x.head) + MultisetUnion(Cons(x.tail.head, x.tail.tail));
      multiset_of(x.head) + MultisetUnion(x.tail);
      MultisetUnion(Cons(x.head, x.tail));
      MultisetUnion(x);
    }
  }
}

lemma perm_merge(xs: List<G>, ys: List<G>)
  ensures multiset_of(merge(xs, ys)) == multiset_of(xs) + multiset_of(ys)
{
}

// sorted-ness lemmas

lemma sorted_sort(xs: List<G>)
  ensures sorted(sort(xs))
{
  sorted_sequences(xs);
  sorted_mergeAll(sequences(xs));
}

ghost predicate AllSorted(x: List<List<G>>)
{
  match x
  case Nil => true
  case Cons(xs, y) => sorted(xs) && AllSorted(y)
}

lemma sorted_sequences(xs: List<G>)
  ensures AllSorted(sequences(xs))
  decreases xs, 0
{
  match xs {
    case Nil =>
    case Cons(a, ys) =>
      match ys {
        case Nil =>
        case Cons(b, zs) =>
          if !Below(a, b) {
            sorted_descending(b, Cons(a, Nil), zs);
          } else {
            sorted_ascending(b, Cons(a, Nil), zs);
          }
      }
  }
}

lemma sorted_descending(a: G, xs: List<G>, ys: List<G>)
  requires (forall y :: y in multiset_of(xs) ==> Below(a, y)) && sorted(xs)
  ensures AllSorted(descending(a, xs, ys))
  decreases ys
{
  if ys.Cons? && !Below(a, ys.head) {
    sorted_descending(ys.head, Cons(a, xs), ys.tail);
  } else {
    calc {
      AllSorted(Cons(Cons(a, xs), sequences(ys)));
      sorted(Cons(a, xs)) && AllSorted(sequences(ys));
      { sorted_sequences(ys); }
      sorted(Cons(a, xs));
      true;
    }
  }
}

lemma sorted_ascending(a: G, xs: List<G>, ys: List<G>)
  requires (forall y :: y in multiset_of(xs) ==> Below(y, a)) && sorted(reverse(xs, Nil))
  ensures AllSorted(ascending(a, xs, ys))
  decreases ys
{
  sorted_insertInMiddle(xs, a, Nil);
  if ys.Cons? && Below(a, ys.head) {
    sorted_ascending(ys.head, Cons(a, xs), ys.tail);
  } else {
    calc {
      AllSorted(Cons(reverse(Cons(a, xs), Nil), sequences(ys)));
      sorted(reverse(Cons(a, xs), Nil)) && AllSorted(sequences(ys));
      { sorted_sequences(ys); }
      sorted(reverse(Cons(a, xs), Nil));
      true;
    }
  }
}

lemma sorted_reverse(xs: List<G>, ys: List<G>)
  requires sorted(reverse(xs, ys))
  ensures sorted(ys)
  ensures forall a,b :: a in multiset_of(xs) && b in multiset_of(ys) ==> Below(a, b)
{
  match xs
  case Nil =>
  case Cons(x, rest) => {
    sorted_reverse(rest, Cons(x, ys));
    assert forall a,b :: a in multiset_of(xs) && b in multiset_of(ys) ==> Below(a, b);
  }
}

lemma sorted_insertInMiddle(xs: List<G>, a: G, ys: List<G>)
  requires sorted(reverse(xs, ys))
  requires forall y :: y in multiset_of(xs) ==> Below(y, a)
  requires forall y :: y in multiset_of(ys) ==> Below(a, y)
  ensures sorted(reverse(xs, Cons(a, ys)))
{
  match xs {
    case Nil =>
    case Cons(b, xs') =>
      calc ==> {
        true;
        { sorted_reverse(xs, ys); }
        sorted(reverse(xs', Cons(b, ys))) && sorted(Cons(a, ys));
        { sorted_replaceSuffix(xs', Cons(b, ys), Cons(a, ys)); }
        sorted(reverse(xs', Cons(a, ys)));
        { sorted_reverse(xs', Cons(b, ys));
          sorted_insertInMiddle(xs', b, Cons(a, ys)); }
        sorted(reverse(xs', Cons(b, Cons(a, ys))));
      }
  }
}

lemma sorted_replaceSuffix(xs: List<G>, ys: List<G>, zs: List<G>)
  requires sorted(reverse(xs, ys)) && sorted(zs)
  requires forall a,b :: a in multiset_of(xs) && b in multiset_of(zs) ==> Below(a, b)
  ensures sorted(reverse(xs, zs))
{
  match xs {
    case Nil =>
    case Cons(c, xs') =>
      sorted_reverse(xs, ys);
      sorted_reverse(xs', Cons(c, ys));
      sorted_replaceSuffix(xs', Cons(c, ys), Cons(c, zs));
  }
}

lemma sorted_mergeAll(x: List<List<G>>)
  requires x != Nil && AllSorted(x)
  ensures sorted(mergeAll(x))
  decreases length(x)
{
  if x.tail != Nil {
    sorted_mergePairs(x);
  }
}

lemma sorted_mergePairs(x: List<List<G>>)
  requires AllSorted(x)
  ensures AllSorted(mergePairs(x))
{
  if x.Cons? && x.tail.Cons? {
    sorted_merge(x.head, x.tail.head);
  }
}

lemma sorted_merge(xs: List<G>, ys: List<G>)
  requires sorted(xs) && sorted(ys)
  ensures sorted(merge(xs, ys))
{
  match xs
  case Nil =>
    assert merge(xs, ys) == ys;
  case Cons(a, xs') =>
    assert (forall z :: z in multiset_of(xs') ==> Below(a, z));
    match ys
    case Nil =>
      assert merge(xs, ys) == xs;
    case Cons(b, ys') =>
      assert (forall z :: z in multiset_of(ys') ==> Below(b, z));
      if Below(a, b) {
        assert merge(xs, ys) == Cons(a, merge(xs', ys));
        var rest := merge(xs', ys);
        MultisetOfMerge(xs', ys);
        assert (forall z :: z in multiset_of(rest) ==> Below(a, z));
        sorted_merge(xs', ys);
      } else {
        assert merge(xs, ys) == Cons(b, merge(xs, ys'));
        var rest := merge(xs, ys');
        MultisetOfMerge(xs, ys');
        assert (forall z :: z in multiset_of(rest) ==> Below(b, z));
        sorted_merge(xs, ys');
      }
}

// -- stability lemmas

lemma stable_sort(g: G, xs: List<G>)
  ensures filter(g, sort(xs)) == filter(g, xs)
{
  calc {
    filter(g, sort(xs));
    // def. sort
    filter(g, mergeAll(sequences(xs)));
    { sorted_sequences(xs); stable_mergeAll(g, sequences(xs)); }
    filter(g, flatten(sequences(xs)));
    { stable_sequences(g, xs); }
    filter(g, xs);
  }
}

lemma stable_sequences(g: G, xs: List<G>)
  ensures filter(g, flatten(sequences(xs))) == filter(g, xs)
  decreases xs, 0
{
  match xs {
    case Nil =>
    case Cons(a, ys) =>
      match ys {
        case Nil =>
          calc {
            flatten(sequences(xs));
            // def. sequences, since xs == Cons(a, Nil)
            flatten(Cons(xs, Nil));
            // def. flatten
            append(xs, flatten(Nil));
            // def. flatten
            append(xs, Nil);
            { append_Nil(xs); }
            xs;
          }
        case Cons(b, zs) =>
          if !Below(a, b) {
            calc {
              filter(g, flatten(sequences(xs)));
              filter(g, flatten(descending(b, Cons(a, Nil), zs)));
              { assert sorted(Cons(a, Nil)); stable_descending(g, b, Cons(a, Nil), zs); }
              filter(g, append(Cons(b, Cons(a, Nil)), zs));
              // in the next couple of steps, unfold the definition of append
              filter(g, Cons(b, append(Cons(a, Nil), zs)));
              filter(g, Cons(b, Cons(a, zs)));
              { filter_Cons_notBelow(g, b, a, zs); }
              filter(g, Cons(a, Cons(b, zs)));
            }
          } else {
            calc {
              filter(g, flatten(sequences(xs)));
              filter(g, flatten(ascending(b, Cons(a, Nil), zs)));
              { stable_ascending(g, b, Cons(a, Nil), zs); }
              filter(g, append(reverse(Cons(b, Cons(a, Nil)), Nil), zs));
              // in the next three steps, unfold the definition of reverse
              filter(g, append(reverse(Cons(a, Nil), Cons(b, Nil)), zs));
              filter(g, append(reverse(Nil, Cons(a, Cons(b, Nil))), zs));
              filter(g, append(Cons(a, Cons(b, Nil)), zs));
              // in the next couple of steps, unfold the definition of append
              filter(g, Cons(a, append(Cons(b, Nil), zs)));
              filter(g, Cons(a, Cons(b, zs)));
            }
          }
      }
  }
}

lemma stable_descending(g: G, a: G, xs: List<G>, ys: List<G>)
  requires sorted(Cons(a, xs))
  ensures filter(g, flatten(descending(a, xs, ys))) == filter(g, append(Cons(a, xs), ys))
  decreases ys
{
  if ys.Cons? && !Below(a, ys.head) {
    calc {
      filter(g, flatten(descending(a, xs, ys)));
      filter(g, flatten(descending(ys.head, Cons(a, xs), ys.tail)));
      { stable_descending(g, ys.head, Cons(a, xs), ys.tail); }
      filter(g, append(Cons(ys.head, Cons(a, xs)), ys.tail));
      filter(g, Cons(ys.head, append(Cons(a, xs), ys.tail)));
      { filter_append_notBelow(g, ys.head, Cons(a, xs), ys.tail); }
      filter(g, append(Cons(a, xs), Cons(ys.head, ys.tail)));
      filter(g, append(Cons(a, xs), ys));
    }
  } else {
    calc {
      filter(g, flatten(descending(a, xs, ys)));
      filter(g, flatten(Cons(Cons(a, xs), sequences(ys))));
      filter(g, append(Cons(a, xs), flatten(sequences(ys))));
      { filter_append(g, Cons(a, xs), flatten(sequences(ys))); }
      append(filter(g, Cons(a, xs)), filter(g, flatten(sequences(ys))));
      { stable_sequences(g, ys); }
      append(filter(g, Cons(a, xs)), filter(g, ys));
      { filter_append(g, Cons(a, xs), ys); }
      filter(g, append(Cons(a, xs), ys));
    }
  }
}

lemma stable_ascending(g: G, a: G, xs: List<G>, ys: List<G>)
  ensures filter(g, flatten(ascending(a, xs, ys))) == filter(g, append(reverse(Cons(a, xs), Nil), ys))
  decreases ys
{
  if ys.Cons? && Below(a, ys.head) {
    calc {
      filter(g, flatten(ascending(a, xs, ys)));
      filter(g, flatten(ascending(ys.head, Cons(a, xs), ys.tail)));
      { stable_ascending(g, ys.head, Cons(a, xs), ys.tail); }
      filter(g, append(reverse(Cons(ys.head, Cons(a, xs)), Nil), ys.tail));
      filter(g, append(reverse(Cons(a, xs), Cons(ys.head, Nil)), ys.tail));
      { filter_append_reverse(g, ys.head, Cons(a, xs), ys.tail); }
      filter(g, append(reverse(Cons(a, xs), Nil), Cons(ys.head, ys.tail)));
      filter(g, append(reverse(Cons(a, xs), Nil), ys));
    }
  } else {
    calc {
      filter(g, flatten(ascending(a, xs, ys)));
      filter(g, flatten(Cons(reverse(Cons(a, xs), Nil), sequences(ys))));
      filter(g, append(reverse(Cons(a, xs), Nil), flatten(sequences(ys))));
      { filter_append(g, reverse(Cons(a, xs), Nil), flatten(sequences(ys))); }
      append(filter(g, reverse(Cons(a, xs), Nil)), filter(g, flatten(sequences(ys))));
      { stable_sequences(g, ys); }
      append(filter(g, reverse(Cons(a, xs), Nil)), filter(g, ys));
      { filter_append(g, reverse(Cons(a, xs), Nil), ys); }
      filter(g, append(reverse(Cons(a, xs), Nil), ys));
    }
  }
}

lemma stable_mergeAll(g: G, x: List<List<G>>)
  requires x != Nil && AllSorted(x)
  ensures filter(g, mergeAll(x)) == filter(g, flatten(x))
  decreases length(x)
{
  if x.tail == Nil {
    calc {
      flatten(x);
      append(x.head, Nil);
      { append_Nil(x.head); }
      x.head;
      mergeAll(x);
    }
  } else {
    calc {
      filter(g, mergeAll(x));
      filter(g, mergeAll(mergePairs(x)));
      { sorted_mergePairs(x); stable_mergeAll(g, mergePairs(x)); }  // induction hypothesis
      filter(g, flatten(mergePairs(x)));
      { stable_mergePairs(g, x); }
      filter(g, flatten(x));
    }
  }
}

lemma stable_mergePairs(g: G, x: List<List<G>>)
  requires AllSorted(x)
  ensures filter(g, flatten(mergePairs(x))) == filter(g, flatten(x))
{
  if x.Cons? && x.tail.Cons? {
    calc {
      filter(g, flatten(mergePairs(x)));
      // def. mergePairs
      filter(g, flatten(Cons(merge(x.head, x.tail.head), mergePairs(x.tail.tail))));
      // def. flatten
      filter(g, append(merge(x.head, x.tail.head), flatten(mergePairs(x.tail.tail))));
      { filter_append(g, merge(x.head, x.tail.head), flatten(mergePairs(x.tail.tail))); }
      append(filter(g, merge(x.head, x.tail.head)), filter(g, flatten(mergePairs(x.tail.tail))));
      { stable_mergePairs(g, x.tail.tail); }  // induction hypothesis
      append(filter(g, merge(x.head, x.tail.head)), filter(g, flatten(x.tail.tail)));
      { stable_merge(g, x.head, x.tail.head); }
      append(filter(g, append(x.head, x.tail.head)), filter(g, flatten(x.tail.tail)));
      { filter_append(g, append(x.head, x.tail.head), flatten(x.tail.tail)); }
      filter(g, append(append(x.head, x.tail.head), flatten(x.tail.tail)));
      { append_associative(x.head, x.tail.head, flatten(x.tail.tail)); }
      filter(g, append(x.head, append(x.tail.head, flatten(x.tail.tail))));
      // def. flatten
      filter(g, append(x.head, flatten(Cons(x.tail.head, x.tail.tail))));
      filter(g, append(x.head, flatten(x.tail)));
      // def. flatten
      filter(g, flatten(Cons(x.head, x.tail)));
      filter(g, flatten(x));
    }
  }
}

lemma stable_merge(g: G, xs: List<G>, ys: List<G>)
  requires sorted(xs)
  ensures filter(g, merge(xs, ys)) == filter(g, append(xs, ys))
{
  match xs {
    case Nil =>
    case Cons(a, xs') =>
      match ys {
        case Nil =>
          append_Nil(xs);
        case Cons(b, ys') =>
          if Below(a, b) {
            // proof for this case is automatic; merge does the same thing as append does
          } else {
            calc {
              filter(g, merge(xs, ys));
              filter(g, Cons(b, merge(xs, ys')));
              { stable_merge(g, xs, ys'); }
              filter(g, Cons(b, append(xs, ys')));
              { filter_append_notBelow(g, b, xs, ys'); }
              filter(g, append(xs, Cons(b, ys')));
              filter(g, append(xs, ys));
            }
        }
      }
  }
}

lemma filter_append(g: G, xs: List<G>, ys: List<G>)
  ensures filter(g, append(xs, ys)) == append(filter(g, xs), filter(g, ys))
{
}

lemma filter_append_notInXs(g: G, b: G, xs: List<G>, ys: List<G>)
  requires forall z <- multiset_of(xs) :: key(g) != key(z)
  ensures filter(g, Cons(b, append(xs, ys))) == filter(g, append(xs, Cons(b, ys)))
{
}

lemma filter_append_notSame(g: G, b: G, xs: List<G>, ys: List<G>)
  requires key(g) != key(b)
  ensures filter(g, append(xs, ys)) == filter(g, append(xs, Cons(b, ys)))
{
}

lemma filter_append_notBelow(g: G, b: G, xs: List<G>, ys: List<G>)
  requires sorted(xs)
  requires xs.Cons? ==> !Below(xs.head, b)
  ensures filter(g, Cons(b, append(xs, ys))) == filter(g, append(xs, Cons(b, ys)))
{
  if key(g) == key(b) {
    filter_append_notInXs(g, b, xs, ys);
  } else {
    calc {
      filter(g, Cons(b, append(xs, ys)));
      // def. filter
      filter(g, append(xs, ys));
      { filter_append_notSame(g, b, xs, ys); }
      filter(g, append(xs, Cons(b, ys)));
    }
  }
}

lemma filter_Cons_notBelow(g: G, b: G, a: G, ys: List<G>)
  requires !Below(a, b)
  ensures filter(g, Cons(b, Cons(a, ys))) == filter(g, Cons(a, Cons(b, ys)))
{
}

lemma filter_append_reverse(g: G, b: G, xs: List<G>, ys: List<G>)
  ensures filter(g, append(reverse(xs, Cons(b, Nil)), ys)) == filter(g, append(reverse(xs, Nil), Cons(b, ys)))
{
  match xs {
    case Nil =>
    case Cons(c, xs') =>
      calc {
        filter(g, append(reverse(xs, Cons(b, Nil)), ys));
        filter(g, append(reverse(Cons(c, xs'), Cons(b, Nil)), ys));
        { append_reverse(Cons(c, xs'), Cons(b, Nil)); }
        filter(g, append(append(reverse(Cons(c, xs'), Nil), Cons(b, Nil)), ys));
        // def. reverse
        filter(g, append(append(reverse(xs', Cons(c, Nil)), Cons(b, Nil)), ys));
        { append_associative(reverse(xs', Cons(c, Nil)), Cons(b, Nil), ys); }
        filter(g, append(reverse(xs', Cons(c, Nil)), append(Cons(b, Nil), ys)));
        // def. append
        filter(g, append(reverse(xs', Cons(c, Nil)), Cons(b, ys)));
        // def. reverse
        filter(g, append(reverse(Cons(c, xs'), Nil), Cons(b, ys)));
        filter(g, append(reverse(xs, Nil), Cons(b, ys)));
      }
  }
}

lemma append_reverse(xs: List, ys: List)
  ensures reverse(xs, ys) == append(reverse(xs, Nil), ys)
{
  match xs {
    case Nil =>
    case Cons(a, xs') =>
      calc {
        reverse(Cons(a, xs'), ys);
        reverse(xs', Cons(a, ys));
        // induction hypothesis
        append(reverse(xs', Nil), Cons(a, ys));
        append(reverse(xs', Nil), append(Cons(a, Nil), ys));
        { append_associative(reverse(xs', Nil), Cons(a, Nil), ys); }
        append(append(reverse(xs', Nil), Cons(a, Nil)), ys);
        // induction hypothesis
        append(reverse(xs', Cons(a, Nil)), ys);
        append(reverse(Cons(a, xs'), Nil), ys);
      }
  }
}
