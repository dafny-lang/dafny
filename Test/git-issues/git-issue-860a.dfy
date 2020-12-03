module A {
  type MZZZ  // gets error "undeclared identifier: #$M"
  function m(): MZZZ
}

module B {
  import A
  type MZZZ<K>
}

