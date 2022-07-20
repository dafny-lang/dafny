class A {
  var x: int;

  constructor() {}

  function method GetX(): int
    reads this
  {
    this.x
  }
}
