class A {
    predicate Valid() reads this {
        true
    }

    constructor() {
        // no-op
    }
}

class B {
    var things: set<A>

    predicate Valid()
        reads this, things
    {
        forall thing | thing in things :: thing.Valid()
    }

    constructor() {
        things := {};
    }
}
