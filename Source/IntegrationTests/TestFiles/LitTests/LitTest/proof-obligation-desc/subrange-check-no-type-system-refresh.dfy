// RUN: %exits-with 4 %verify --show-proof-obligation-expressions --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method SubrangeCheck<T, U>(o: object?, p: T --> U, r: T ~> U, i: int) {
    var nonNullVar: object := o;
    var totalVar: T -> U := p;
    var partialVar: T --> U := r;
    var natVar: nat := i;
}
