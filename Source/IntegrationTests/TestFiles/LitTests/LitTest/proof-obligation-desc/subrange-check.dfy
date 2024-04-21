// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// TODO: %diff "%s.expect" "%t"

method SubrangeCheck(o: object?, p: () --> (), r: () ~> (), i: int) {
    var nonNullVar: object := o;
    var totalVar: () -> () := p;
    var partialVar: () --> () := r;
    var natVar: nat := i;
}