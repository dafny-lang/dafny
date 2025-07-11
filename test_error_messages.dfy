class TestClass {
  var x: int

  method TestModifies() {
    var obj: TestClass? := new TestClass;
    obj.x := 5; // This should trigger a modifies clause error
  }

  method TestNullAccess() {
    var obj: TestClass? := null;
    var y := obj.x; // This should trigger a null access error
  }
}
