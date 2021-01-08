module A {
  export provides a
  const a := 10;
  const b := 20;
}

module B {
  import A
  method m() {
    assert A.a == 10; // a is known, but not its value
    // assert A.b == 20; // b is not known through A`A
  }
}
