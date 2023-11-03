// RUN: %testDafnyForEachResolver "%s"


datatype Maybe = Nothing | Just
ghost predicate bad(e:Maybe)
{
    forall i :: 0 <= i < 1 ==>
        0 == match e
            case Nothing => 0
            case Just => 0
}

