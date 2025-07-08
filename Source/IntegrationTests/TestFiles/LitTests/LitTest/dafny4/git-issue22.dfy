// RUN: %testDafnyForEachResolver "%s" -- --allow-warnings


ghost predicate bad()
{
    forall i :: i in {1}
}
