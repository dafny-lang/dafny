module A {
    type M<K> // eliminating the type parameter eliminates the error
}
module B {
    type M   // gets error "undeclared identifier: #$M"
    function m():M
}
module C {
    import A
    import B
    type T =  nat // removing this eliminates the error
}

