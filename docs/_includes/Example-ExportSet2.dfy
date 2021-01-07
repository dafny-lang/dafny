module A {
  export reveals a
  const a := 10;
  const b := 20;
}

module B {
  import A
  method m() {
    assert A.a == 10; // a and its value are known
    // assert A.b == 20; // b is not known through A`A
  }
}
