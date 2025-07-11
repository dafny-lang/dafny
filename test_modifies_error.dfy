class TestClass {
  var x: int
}

method TestModifies(obj: TestClass)
  modifies {}  // Empty modifies clause
{
  obj.x := 5; // This should trigger our new modifies clause error
}
