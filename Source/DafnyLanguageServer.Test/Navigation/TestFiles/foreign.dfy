class A {
  var x: int;

  constructor() {}

  function GetX(): int
    reads this
  {
    this.x
  }
}
