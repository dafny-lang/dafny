/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/
/**
A collection of predicates that establish whether commonly known properties on relations, 
such as reflexivity and transitivity, hold for a particular relation. 
These properties can only be applied to relations that operate on value types, 
as opposed to relations that operate on sets in general.

Also contains predicates that establish how a value relates to a set,
such as whether it is the least or minimal element.
*/
module Std.Relations {

  ghost predicate Reflexive<T(!new)>(relation: (T, T) -> bool) {
    forall x :: relation(x, x)
  }

  ghost predicate Irreflexive<T(!new)>(relation: (T, T) -> bool) {
    forall x :: !relation(x, x)
  }

  ghost predicate Symmetric<T(!new)>(relation: (T, T) -> bool) {
    forall x, y :: relation(x, y) <==> relation(y, x)
  }

  ghost predicate AntiSymmetric<T(!new)>(relation: (T, T) -> bool) {
    forall x, y :: relation(x, y) && relation(y, x) ==> x == y
  }

  ghost predicate Asymmetric<T(!new)>(relation: (T, T) -> bool) {
    forall x, y :: relation(x, y) ==> !relation(y, x)
  }

  lemma AsymmetricIsAntiSymmetric<T(!new)>(relation: (T, T) -> bool)
    ensures Asymmetric(relation) ==> AntiSymmetric(relation)
  {}

  lemma AsymmetricIsIrreflexive<T(!new)>(relation: (T, T) -> bool)
    ensures Asymmetric(relation) ==> Irreflexive(relation)
  {}

  ghost predicate Connected<T(!new)>(relation: (T, T) -> bool) {
    forall x, y :: x != y ==> relation(x, y) || relation(y, x)
  }

  ghost predicate StronglyConnected<T(!new)>(relation: (T, T) -> bool) {
    forall x, y :: relation(x, y) || relation(y, x)
  }

  ghost predicate Transitive<T(!new)>(relation: (T, T) -> bool) {
    forall x, y, z :: relation(x, y) && relation(y, z) ==> relation(x, z)
  }

  ghost predicate TotalOrdering<T(!new)>(relation: (T, T) -> bool) {
    && Reflexive(relation)
    && AntiSymmetric(relation)
    && Transitive(relation)
    && StronglyConnected(relation)
  }

  ghost predicate StrictTotalOrdering<T(!new)>(relation: (T, T) -> bool) {
    && Irreflexive(relation)
    && AntiSymmetric(relation)
    && Transitive(relation)
    && Connected(relation)
  }

  ghost predicate PreOrdering<T(!new)>(relation: (T, T) -> bool) {
    && Reflexive(relation)
    && Transitive(relation)
  }

  ghost predicate PartialOrdering<T(!new)>(relation: (T, T) -> bool) {
    && Reflexive(relation)
    && Transitive(relation)
    && AntiSymmetric(relation)
  }

  ghost predicate EquivalenceRelation<T(!new)>(relation: (T, T) -> bool) {
    && Reflexive(relation)
    && Symmetric(relation)
    && Transitive(relation)
  }

  ghost predicate IsLeast<T>(lessOrEqual: (T, T) -> bool, least: T, s: set<T>) {
    least in s && forall x | x in s :: lessOrEqual(least, x)
  }

  ghost predicate IsMinimal<T>(lessOrEqual: (T, T) -> bool, minimal: T, s: set<T>) {
    minimal in s && forall x | x in s && lessOrEqual(x, minimal) :: lessOrEqual(minimal, x)
  }

  ghost predicate IsGreatest<T>(lessOrEqual: (T, T) -> bool, greatest: T, s: set<T>) {
    greatest in s && forall x | x in s :: lessOrEqual(x, greatest)
  }

  ghost predicate IsMaximal<T>(lessOrEqual: (T, T) -> bool, maximal: T, s: set<T>) {
    maximal in s && forall x | x in s && lessOrEqual(maximal, x) :: lessOrEqual(x, maximal)
  }

  ghost predicate SortedBy<T>(lessOrEqual: (T, T) -> bool, xs: seq<T>) {
    forall i, j | 0 <= i < j < |xs| :: lessOrEqual(xs[i], xs[j])
  }
}
