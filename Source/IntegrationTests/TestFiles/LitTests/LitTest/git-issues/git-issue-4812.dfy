// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait ProblemHolder<T(!new, ==)> {
  ghost function Solution(): T

  predicate Problem(solution: T)
    ensures Solution() == solution
}

trait Instantiation extends ProblemHolder<int> {
  ghost function Solution(): int

  predicate Problem(solution: int)
    ensures Solution() == solution
}