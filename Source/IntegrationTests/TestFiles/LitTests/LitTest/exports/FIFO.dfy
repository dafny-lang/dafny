// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

include "Queue.dfyi"

module FIFO refines Queue {
    type Item = int

    method Init() returns (q: Queue) {
        q := [];
    }

    method Push(item: Item, q: Queue) returns (q': Queue) {
        return q + [item];
    }

    method Pop(q: Queue) returns (item: Item, q': Queue)
        ensures item == q[0]
    {
        item := q[0];
        q' := q[1..];
    }
}

module MainImpl refines MainSpec {
    import Q = FIFO

    method Main()
    {
        var q := Q.Init();
        q := Q.Push(0, q);
        q := Q.Push(1, q);
        q := Q.Push(2, q);

        var n: int;
        n, q := Q.Pop(q);
        print n, "\n";
        n, q := Q.Pop(q);
        print n, "\n";
        n, q := Q.Pop(q);
        print n, "\n";
    }
}
