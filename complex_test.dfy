method Test() {
  var a := .5;
  var b := 1.;
  var c := 1.23e5;
  var d := .125e3;
  
  // Test that field access still works
  var p := (a, b);
  var x := p.0;
  var y := p.1;
  
  // Test method calls
  assert a == 0.5;
}
