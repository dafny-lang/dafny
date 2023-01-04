class {:autocontracts} A {
    predicate Valid() {
        true
    }

    constructor() {
        // no-op
    }
}

class {:autocontracts} B {
    var things: set<A>

    predicate Valid()
        reads things
    {
        forall thing | thing in things :: thing.Valid()
    }

    constructor() {
        things := {};
    }
}
