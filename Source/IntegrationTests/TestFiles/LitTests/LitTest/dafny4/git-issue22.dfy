// RUN: %testDafnyForEachResolver "%s"


ghost predicate bad()
{
    forall i :: i in {1}
}
