class Test {
  var x: int
}

method Parameters(i: Test, ghost mem_i: (object, field))
  requires mem_i == locals`i
{
  var mem_i2 := locals`i;
}

method CallParameters() {
  var t := new Test();
  var i := new Test();
  Parameters(t, locals`i); // Error: Precondition could not hold. Not the same local variable
}